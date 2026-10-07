module

public import RequestProject.LQT.Core
public import RequestProject.LQT.UsageVec

/-!
# Desugaring into the core calculus (§7.2.3, Figure 12b, Appendix A.2)

Paper location: §7.2.3 "Translating terms" (Figure 12b "Desugaring (subset)") and its complete
version in Appendix A.2 (Figure 15 "Desugaring").  The start and end of each part is marked by
`-- [PAPER ▶ START]` / `-- [PAPER ◀ END]` comments, and each case of the translation is
labelled with the typing rule it handles.

Given a derivation `d` of `Q ; Γ ⊢ e : τ` we build a core expression `⟦d⟧_z` such that
`⟦Γ⟧, z :₁ ⟦Q⟧ ⊢ ⟦d⟧_z : ⟦τ⟧` (**Theorem 7.1**, `desugar_typed`).  As in the paper the
translation is defined by recursion on the typing derivation (`HasType` is `Type`-valued) and
passes the evidence for `Q` in the variable `z`.

In the de Bruijn setting it is convenient to define the translation into an arbitrary larger
context: `desugarAt d ρ z` places the variables of `Γ` along an injective renaming `ρ` and the
evidence variable at index `z` (`desugar d = desugarAt d Fin.succ 0`).

A `let` with a signature `∀ā. Q ⇒ τ₁` is translated to a polymorphic core `let` binding a
function `⟦Q⟧ →₁ ⟦τ₁⟧`, and `let pack x = e₁ in e₂` to the elimination of a core existential
pair.
-/

@[expose] public section

noncomputable section

namespace LQT

open SConstr

variable {P : Type}

-- [PAPER ▶ START] §7.2.3 "Translating terms" › Figure 12b "Desugaring (subset)" and Appendix A.2 ›
--   Figure 15 "Desugaring": the translation `⟦Q ; Γ ⊢ e : τ⟧_z`, by recursion on typing derivations
/-- `ω`-scaling, as a shorthand. -/
local notation "ω•" Q => ((Mult.omega : Mult) • Q)

/-- The translation of `let`-bindings without signature (rule E_Let).  In context `m`, the
evidence `z : ⟦π·Q₁ ⊗ Q₂⟧` is split into `z₁ : ⟦π·Q₁⟧` and `z₂ : ⟦Q₂⟧`; the bound variable
receives the translation of `e₁` abstracted over the evidence for `Q` (when `Q ≠ ε`), and `e₂`
is translated with evidence `z₂`. -/
def dsLet {sig : DataSig P} {k n m : Nat} (π : Mult) (Q Q₁ Q₂ : SConstr (Atom P k))
    (ρ : Fin n → Fin m) (z : Fin m)
    (t₁ : ∀ {m' : Nat}, (Fin n → Fin m') → Fin m' → CTm sig k m')
    (t₂ : ∀ {m' : Nat}, (Fin (n + 1) → Fin m') → Fin m' → CTm sig k m') : CTm sig k m :=
  .letPair (.prim (.split (π • Q₁) Q₂) (.var z))
    (match π with
      | .one =>
        .let_ .one
          (if Q = 0 then .let_ .one (.prim (.coe Q₁ (Q₁ + Q)) (.var 0)) (t₁ (shift (shift (shift ρ))) 0)
           else .lam (.let_ .one (.prim (.join Q₁ Q) (.pair (.var (Fin.succ 0)) (.var 0)))
                  (t₁ (shift (shift (shift (shift ρ)))) 0)))
          (t₂ (liftR (shift (shift ρ))) (Fin.succ (Fin.succ 0)))
      | .omega =>
        .letUr (.prim (.urEv Q₁) (.var 0))
          (.let_ .omega
            (if Q = 0 then
              .let_ .one (.prim (.coe (ω• Q₁) (Q₁ + Q)) (.var 0))
                (t₁ (shift (shift (shift (shift ρ)))) 0)
             else .lam (.let_ .one (.prim (.join Q₁ Q)
                    (.pair (.prim (.coe (ω• Q₁) Q₁) (.var (Fin.succ 0))) (.var 0)))
                  (t₁ (shift (shift (shift (shift (shift ρ))))) 0)))
            (t₂ (liftR (shift (shift (shift ρ)))) (Fin.succ (Fin.succ (Fin.succ 0))))))

/-- The translation of `let`-bindings with a signature `∀ā. Q ⇒ τ₁` (rule E_LetSig): as
`dsLet`, but the bound expression is generalised over the `j` type variables `ā`. -/
def dsLetSig {sig : DataSig P} {k n m : Nat} (π : Mult) (j : Nat) (Q : SConstr (Atom P (k + j)))
    (Q₁ Q₂ : SConstr (Atom P k)) (ρ : Fin n → Fin m) (z : Fin m)
    (t₁ : ∀ {m' : Nat}, (Fin n → Fin m') → Fin m' → CTm sig (k + j) m')
    (t₂ : ∀ {m' : Nat}, (Fin (n + 1) → Fin m') → Fin m' → CTm sig k m') : CTm sig k m :=
  .letPair (.prim (.split (π • Q₁) Q₂) (.var z))
    (match π with
      | .one =>
        .letGen .one j
          (if Q = 0 then
              .let_ .one (.prim (.coe (Q₁.wk j) (Q₁.wk j + Q)) (.var 0))
                (t₁ (shift (shift (shift ρ))) 0)
           else .lam (.let_ .one (.prim (.join (Q₁.wk j) Q) (.pair (.var (Fin.succ 0)) (.var 0)))
                  (t₁ (shift (shift (shift (shift ρ)))) 0)))
          (t₂ (liftR (shift (shift ρ))) (Fin.succ (Fin.succ 0)))
      | .omega =>
        .letUr (.prim (.urEv Q₁) (.var 0))
          (.letGen .omega j
            (if Q = 0 then
              .let_ .one (.prim (.coe ((ω• Q₁).wk j) (Q₁.wk j + Q)) (.var 0))
                (t₁ (shift (shift (shift (shift ρ)))) 0)
             else .lam (.let_ .one (.prim (.join (Q₁.wk j) Q)
                    (.pair (.prim (.coe ((ω• Q₁).wk j) (Q₁.wk j)) (.var (Fin.succ 0))) (.var 0)))
                  (t₁ (shift (shift (shift (shift (shift ρ))))) 0)))
            (t₂ (liftR (shift (shift (shift ρ)))) (Fin.succ (Fin.succ (Fin.succ 0))))))

/-- The desugaring `⟦d⟧` of a typing derivation `d`, into a context of size `m` in which the
variables of `Γ` are placed along `ρ` and the evidence for `Q` is the variable `z`. -/
def desugarAt {D : LDomain (Atom P)} {sig : DataSig P} : {k n : Nat} →
    {Q : SConstr (Atom P k)} → {Γ : Fin n → Scheme P k} → {u : Fin n → Usage} →
    {e : Tm sig k n} → {τ : Ty P k} →
    HasType D sig Q Γ u e τ → {m : Nat} → (Fin n → Fin m) → Fin m → CTm sig k m
  -- [PAPER] Appendix A.2 › Figure 15, case of rule E_Var (also in Figure 12b)
  | _, _, _, _, _, _, _, .var (x := x) (σ := σ) _ _ _, _, ρ, z =>
    if σ.Q = 0 then .letUnit (.prim .drop (.var z)) (.var (ρ x)) else .app (.var (ρ x)) (.var z)
  -- (data constructors: no separate case in the paper)
  | _, _, _, _, _, _, _, .con _ T i _, _, _, z => .letUnit (.prim .drop (.var z)) (.con T i)
  -- [PAPER] Appendix A.2 › Figure 15, case of rule E_Abs
  | _, _, _, _, _, _, _, .lam d, _, ρ, z => .lam (desugarAt d (liftR ρ) z.succ)
  -- [PAPER] Appendix A.2 › Figure 15, case of rule E_App (both multiplicities)
  | _, _, _, _, _, _, _, .app (Q₁ := Q₁) (Q₂ := Q₂) (π := π) d₁ d₂, _, ρ, z =>
    .letPair (.prim (.split Q₁ (π • Q₂)) (.var z))
      (match π with
        | .one => .app (desugarAt d₁ (shift (shift ρ)) 0) (desugarAt d₂ (shift (shift ρ)) (Fin.succ 0))
        | .omega =>
          .letUr (.prim (.urEv Q₂) (.var (Fin.succ 0)))
            (.app (desugarAt d₁ (shift (shift (shift ρ))) (Fin.succ 0))
              (.let_ .one (.prim (.coe (ω• Q₂) Q₂) (.var 0))
                (desugarAt d₂ (shift (shift (shift (shift ρ)))) 0))))
  -- [PAPER] Appendix A.2 › Figure 15, case of rule E_Pack (also in Figure 12b)
  | _, _, _, _, _, _, _, .pack (Q := Q) (mul := mul) (pred := pred) (ar := ar) (args := args) υs d,
      _, ρ, z =>
    .letPair (.prim (.split Q ((exqC _ mul pred ar args).tsubst (instSub υs))) (.var z))
      (.pack (desugarAt d (shift (shift ρ)) 0) (.var (Fin.succ 0)))
  -- [PAPER] Appendix A.2 › Figure 15, case of rule E_Unpack (also in Figure 12b)
  | _, _, _, _, _, _, _, .unpack (j := j) (Q₁ := Q₁) (Q₂ := Q₂) (mul := mul) (pred := pred)
      (ar := ar) (args := args) d₁ d₂, _, ρ, z =>
    .letPair (.prim (.split Q₁ Q₂) (.var z))
      (.unpack j (desugarAt d₁ (shift (shift ρ)) 0)
        (.let_ .one (.prim (.join (Q₂.wk j) (exqC _ mul pred ar args))
            (.pair (.var (Fin.succ (Fin.succ (Fin.succ 0)))) (.var (Fin.succ 0))))
          (.let_ .one (.var (Fin.succ 0))
            (desugarAt d₂ (liftR (shift (shift (shift (shift (shift ρ)))))) (Fin.succ 0)))))
  -- [PAPER] Appendix A.2 › Figure 15, case of rule E_Let (both multiplicities; see `dsLet`)
  | _, _, _, _, _, _, _, .let_ (Q := Q) (Q₁ := Q₁) (Q₂ := Q₂) (π := π) d₁ d₂, _, ρ, z =>
    dsLet π Q Q₁ Q₂ ρ z (fun ρ' z' => desugarAt d₁ ρ' z') (fun ρ' z' => desugarAt d₂ ρ' z')
  -- [PAPER] Appendix A.2 › Figure 15, case of rule E_LetSig (both multiplicities; see `dsLetSig`)
  | _, _, _, _, _, _, _, .letSig (Q₁ := Q₁) (Q₂ := Q₂) (π := π) (σ := σ) d₁ d₂, _, ρ, z =>
    dsLetSig π σ.j σ.Q Q₁ Q₂ ρ z (fun ρ' z' => desugarAt d₁ ρ' z')
      (fun ρ' z' => desugarAt d₂ ρ' z')
  -- [PAPER] Appendix A.2 › Figure 15, case of rule E_Case (both multiplicities)
  | _, _, _, _, _, _, _, .case (Q₁ := Q₁) (Q₂ := Q₂) (π := π) (T := T) d ds, _, ρ, z =>
    .letPair (.prim (.split (π • Q₁) Q₂) (.var z))
      (match π with
        | .one =>
          .case .one (desugarAt d (shift (shift ρ)) 0) T
            (fun i => desugarAt (ds i) (liftRN _ (shift (shift ρ))) (Fin.natAdd _ (Fin.succ 0)))
        | .omega =>
          .letUr (.prim (.urEv Q₁) (.var 0))
            (.case .omega (.let_ .one (.prim (.coe (ω• Q₁) Q₁) (.var 0))
                (desugarAt d (shift (shift (shift (shift ρ)))) 0)) T
              (fun i => desugarAt (ds i) (liftRN _ (shift (shift (shift ρ))))
                (Fin.natAdd _ (Fin.succ (Fin.succ 0))))))
  -- [PAPER] Appendix A.2 › Figure 15, case of rule E_Sub (also in Figure 12b)
  | _, _, _, _, _, _, _, .sub (Q := Q) (Q₁ := Q₁) d _, _, ρ, z =>
    .let_ .one (.prim (.coe Q Q₁) (.var z)) (desugarAt d (shift ρ) 0)

/-- The desugaring `⟦d⟧_z` of a derivation of `Q ; Γ ⊢ e : τ`, in the context `⟦Γ⟧, z :₁ ⟦Q⟧`
(the evidence variable `z` is the variable `0`). -/
def desugar {D : LDomain (Atom P)} {sig : DataSig P} {k n : Nat} {Q : SConstr (Atom P k)}
    {Γ : Fin n → Scheme P k} {u : Fin n → Usage} {e : Tm sig k n} {τ : Ty P k}
    (d : HasType D sig Q Γ u e τ) : CTm sig k (n + 1) :=
  desugarAt d Fin.succ 0

-- [PAPER ◀ END] §7.2.3 › Figure 12b / Appendix A.2 › Figure 15

end LQT
