module

public import RequestProject.LH.Syntax

/-!
# Typing rules of `λq→` (Linear Haskell, §3.2 Figure 6 and §3.3)

A typing context `x₁ :_{π₁} A₁, …` is split into its *types* `Γ : Fin n → S.Ty m` and its
*multiplicities* `u : Fin n → Usage m` (a usage vector; usage `0` means that the variable does
not occur in the paper's context).  The paper's context operations become pointwise operations
on usage vectors: `Γ + Δ` is `u + v`, and `π Γ` is `Usage.nz π • u`.  As the paper suggests
("one may want to think of the types in Γ as inputs of the judgement, and the multiplicities as
outputs") the types are shared by all premises, and only the usage vectors are combined.

`HasType S Γ u t A` is the judgement `Γ ⊢ t : A` of Figure 6.

**Typo in rule (abs).**  Figure 6 prints the conclusion of (abs) as
`Γ ⊢ λ_π (x:A). t : A →_q B`, with an unrelated multiplicity `q`; with an arbitrary `q`
the system would be unsound (a non-linear function could be given a linear type).  We use the
evidently intended `A →_π B`.
-/

@[expose] public section

namespace LH

variable {S : Sig}

-- [PAPER ▶ START] §3.2 › Figure 6 "Typing rules" and §3.3 "Data constructors and case expressions"
/-- The typing judgement `Γ ⊢ t : A` of `λq→`, with context types `Γ` and multiplicities `u`. -/
inductive HasType (S : Sig) : {m n : Nat} → (Fin n → S.Ty m) → (Fin n → Usage m) →
    Tm S m n → S.Ty m → Prop
  /-- (var) `ω Γ + x :_1 A ⊢ x : A` -/
  | var {m n} {Γ : Fin n → S.Ty m} {u : Fin n → Usage m} (x : Fin n) (v : Fin n → Usage m)
      (hu : u = (Usage.omega : Usage m) • v + Pi.single x 1) :
      HasType S Γ u (.var x) (Γ x)
  /-- (abs) from `Γ, x :_π A ⊢ t : B` infer `Γ ⊢ λ_π (x:A). t : A →_π B` -/
  | lam {m n} {Γ : Fin n → S.Ty m} {u : Fin n → Usage m} {π : Mult m} {A B : S.Ty m}
      {t : Tm S m (n + 1)} :
      HasType S (Fin.cons A Γ) (Fin.cons (.nz π) u) t B →
      HasType S Γ u (.lam π A t) (.arr A π B)
  /-- (app) from `Γ ⊢ t : A →_π B` and `Δ ⊢ s : A` infer `Γ + π Δ ⊢ t s : B` -/
  | app {m n} {Γ : Fin n → S.Ty m} {u u₁ u₂ : Fin n → Usage m} {t s : Tm S m n} {π : Mult m}
      {A B : S.Ty m} :
      HasType S Γ u₁ t (.arr A π B) → HasType S Γ u₂ s A →
      u = u₁ + Usage.nz π • u₂ →
      HasType S Γ u (.app t s) B
  /-- (m.abs) from `Γ ⊢ t : A` with `p` fresh for `Γ` infer `Γ ⊢ λp. t : ∀p. A` (freshness is
  expressed by weakening `Γ`: the variable `p` does not occur in it) -/
  | mlam {m n} {Γ : Fin n → S.Ty m} {u : Fin n → Usage m} {t : Tm S (m + 1) n}
      {A : S.Ty (m + 1)} :
      HasType S (fun x => (Γ x).wk) (fun x => Usage.wk (u x)) t A →
      HasType S Γ u (.mlam t) (.all A)
  /-- (m.app) from `Γ ⊢ t : ∀p. A` infer `Γ ⊢ t π : A[π/p]` -/
  | mapp {m n} {Γ : Fin n → S.Ty m} {u : Fin n → Usage m} {t : Tm S m n}
      {A : S.Ty (m + 1)} {π : Mult m} :
      HasType S Γ u t (.all A) →
      HasType S Γ u (.mapp t π) (A.subst (Fin.cons π Mult.var))
  /-- (con) from `Δᵢ ⊢ tᵢ : Aᵢ[π⃗]` infer `ω Γ + Σᵢ μᵢ[π⃗] Δᵢ ⊢ c_k t₁ … t_{n_k} : D π⃗` -/
  | con {m n} {Γ : Fin n → S.Ty m} {u : Fin n → Usage m} {d : S.Dn} {k : Fin (S.ncons d)}
      {args : Fin (S.arity d k) → Tm S m n} {ps : Fin (S.np d) → Mult m}
      (v : Fin n → Usage m) (w : Fin (S.arity d k) → Fin n → Usage m) :
      (∀ i, HasType S Γ (w i) (args i) ((S.fieldTy d k i).subst ps)) →
      u = (Usage.omega : Usage m) • v + ∑ i, Usage.nz ((S.fieldMult d k i).subst ps) • w i →
      HasType S Γ u (.con d k args) (.data d ps)
  /-- (case) from `Γ ⊢ t : D π⃗` and, for each constructor,
  `Δ, x₁ :_{π μ₁[π⃗]} A₁[π⃗], … ⊢ u_k : C`, infer `π Γ + Δ ⊢ case_π t of {…} : C` -/
  | case {m n} {Γ : Fin n → S.Ty m} {u u₁ u₂ : Fin n → Usage m} {π : Mult m} {t : Tm S m n}
      {d : S.Dn} {ps : Fin (S.np d) → Mult m}
      {brs : (k : Fin (S.ncons d)) → Tm S m (n + S.arity d k)} {C : S.Ty m} :
      HasType S Γ u₁ t (.data d ps) →
      (∀ k, HasType S (Fin.append Γ (fun i => (S.fieldTy d k i).subst ps))
        (Fin.append u₂ (fun i => Usage.nz (π * (S.fieldMult d k i).subst ps))) (brs k) C) →
      u = Usage.nz π • u₁ + u₂ →
      HasType S Γ u (.case π t d brs) C
  /-- (let) from `Γᵢ ⊢ tᵢ : Aᵢ` and `Δ, x₁ :_π A₁ … xₙ :_π Aₙ ⊢ u : C` infer
  `Δ + π Σᵢ Γᵢ ⊢ let_π x₁ : A₁ = t₁ … in u : C` -/
  | lett {m n} {Γ : Fin n → S.Ty m} {u u₂ : Fin n → Usage m} {π : Mult m} {j : Nat}
      {tys : Fin j → S.Ty m} {rhs : Fin j → Tm S m n} {body : Tm S m (n + j)} {C : S.Ty m}
      (w : Fin j → Fin n → Usage m) :
      (∀ i, HasType S Γ (w i) (rhs i) (tys i)) →
      HasType S (Fin.append Γ tys) (Fin.append u₂ (fun _ => Usage.nz π)) body C →
      u = u₂ + Usage.nz π • ∑ i, w i →
      HasType S Γ u (.lett π j tys rhs body) C
-- [PAPER ◀ END] §3.2 › Figure 6

end LH
