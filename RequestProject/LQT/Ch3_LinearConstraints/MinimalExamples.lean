module

public import RequestProject.LQT.Ch3_LinearConstraints.ExampleSetting
public import RequestProject.LQT.Ch5_QualifiedTypeSystem.TypingInv
public import RequestProject.LQT.Ch6_ConstraintInference.AtomicSolver

/-!
# The minimal examples of §3.1

Paper location: §3.1 "Minimal Examples" (Dithering, Neglecting, Overusing, and the accepted
`notNeglecting`).

The examples use a linear constraint `C` consumed by `useC :: C ⊸ Int`, and the linear
`const :: a ⊸ b → a`; the setting is described in `ExampleSetting.lean`.

We prove:

* `notNeglecting_typed`: `const useC 10` is accepted, `C ; Γ ⊢ const useC 10 : Int`;
* `notNeglecting_inferred`, `notNeglecting_typed_by_inference`: it is also accepted by the
  inference algorithm of §6 (constraint generation followed by the solver with the atomic solver
  of Figure 10b), which yields the typing derivation by Lemmas 6.4 and 6.5;
* `neglecting_rejected`: `const 10 useC` is rejected, at *every* type and usage;
* `overusing_rejected`: `(useC, useC)` is rejected, at every type and usage;
* `dithering_rejected`: `λx. case x of { True → useC ; False → 10 }` is rejected, at every type,
  usage and multiplicity of the `case`.

The rejections are proved with the inversion lemmas of
`Ch5_QualifiedTypeSystem/TypingInv.lean` and a counting
argument: in this domain, entailment from a constraint in which `C` is not unrestricted
preserves the number of linear copies of `C` (`ent_count`).
-/

@[expose] public section

namespace LQT

namespace Examples

-- [PAPER ▶ START] §3.1 "Minimal Examples": the example programs

/-- `useC`. -/
def useC : Tm exSig 0 2 := .var 0
/-- `const`. -/
def constE : Tm exSig 0 2 := .var 1
/-- The literal `10`. -/
def ten {n : Nat} : Tm exSig 0 n := .con 0 ⟨0, by decide⟩

/-- `notNeglecting = const useC 10` (accepted). -/
def notNeglecting : Tm exSig 0 2 := .app (.app constE useC) ten

/-- `neglecting = const 10 useC` (rejected). -/
def neglecting : Tm exSig 0 2 := .app (.app constE ten) useC

/-- `overusing = (useC, useC)` (rejected). -/
def overusing : Tm exSig 0 2 := .app (.app (.con 2 ⟨0, by decide⟩) useC) useC

/-- The alternatives of `if x then useC else 10`: `True → useC`, `False → 10`.  Under the
binder `x`, `useC` has index `1`. -/
def ditheringAlts : (i : Fin (exSig.ncons 1)) → Tm exSig 0 (exSig.arity 1 i + 3) :=
  fun i => if i.val = 0 then (.var 1 : Tm exSig 0 3) else (ten : Tm exSig 0 3)

/-- `dithering = λx. if x then useC else 10`, with `if` a `case` of multiplicity `π` on
`Bool` (rejected for every `π`). -/
def dithering (π : Mult) : Tm exSig 0 2 := .lam (.case π (.var 0) 1 ditheringAlts)

-- [PAPER ◀ END] §3.1, the example programs

-- [PAPER ▶ START] §3.1 "Minimal Examples": `notNeglecting` is accepted, `neglecting`,
--   `overusing` and `dithering` are rejected

/-- `notNeglecting = const useC 10` is accepted: `C ; Γ ⊢ const useC 10 : Int`. -/
theorem notNeglecting_typed :
    ∃ u : Fin 2 → Usage, Nonempty (HasType exD exSig givenC exΓ u notNeglecting intTy) := by
  have d₁₁ := HasType.var (D := exD) (sig := exSig) (Γ := exΓ) (x := 1) (σ := constScheme) 0
    ![intTy, intTy] rfl
  have d₁₂ := HasType.var (D := exD) (sig := exSig) (Γ := exΓ) (x := 0) (σ := useCScheme) 0
    Fin.elim0 rfl
  have d₂ := HasType.con (D := exD) (sig := exSig) (Γ := exΓ) 0 0 ⟨0, by decide⟩ Fin.elim0
  have e₁ : constScheme.τ.subst (instSub ![intTy, intTy]) =
      (.arr .one intTy (.arr .omega intTy intTy) : Ty Unit 0) := rfl
  have e₂ : useCScheme.τ.subst (instSub (Fin.elim0 : Fin 0 → Ty Unit 0)) = intTy := by
    simp only [useCScheme, intTy, Ty.subst]
    congr 1; funext l; exact l.elim0
  rw [e₁] at d₁₁
  rw [e₂] at d₁₂
  refine ⟨_, ⟨.sub (.app (.app d₁₁ d₁₂) d₂) ?_⟩⟩
  apply (exD_lawful 0).entails_of_eq
  simp [constScheme, useCScheme, SConstr.tsubst]
  exact (givenC_tsubst _).symm

/-- `neglecting = const 10 useC` is rejected: no typing derivation with the given `C`, whatever
the type and the usage of the context. -/
theorem neglecting_rejected (u : Fin 2 → Usage) (τ : Ty Unit 0) :
    IsEmpty (HasType exD exSig givenC exΓ u neglecting τ) := by
  refine ⟨fun d => ?_⟩
  obtain ⟨Q₁, Q₂, u₁, u₂, π, τ₁, h, ⟨d₁⟩, ⟨d₂⟩⟩ := HasType.app_inv exD_lawful d
  obtain ⟨Q₁₁, Q₁₂, u₁₁, u₁₂, π', τ₁', h₁, ⟨d₁₁⟩, -⟩ := HasType.app_inv exD_lawful d₁
  obtain ⟨τs, -, hty⟩ := HasType.var_inv exD_lawful d₁₁
  obtain ⟨τs₂, h₂, -⟩ := HasType.var_inv exD_lawful d₂
  simp [exΓ, constScheme, Ty.subst] at hty
  obtain ⟨-, -, rfl, -⟩ := hty
  change (exD 0).Entails Q₂ (SConstr.tsubst _ givenC) at h₂
  rw [givenC_tsubst] at h₂
  obtain ⟨hU, -⟩ := ent_count h (by simp)
  simp only [SConstr.add_U, SConstr.omega_smul_U, Finset.mem_union, Multiset.mem_toFinset,
    not_or] at hU
  obtain ⟨-, hU₂, hL₂⟩ := hU
  obtain ⟨-, hc⟩ := ent_count h₂ hU₂
  simp only [givenC_L, Multiset.count_singleton_self] at hc
  exact hL₂ (Multiset.count_pos.mp (by omega))

/-- `overusing = (useC, useC)` is rejected. -/
theorem overusing_rejected (u : Fin 2 → Usage) (τ : Ty Unit 0) :
    IsEmpty (HasType exD exSig givenC exΓ u overusing τ) := by
  refine ⟨fun d => ?_⟩
  obtain ⟨Q₁, Q₂, u₁, u₂, π, τ₁, h, ⟨d₁⟩, ⟨d₂⟩⟩ := HasType.app_inv exD_lawful d
  obtain ⟨Q₁₁, Q₁₂, u₁₁, u₁₂, π', τ₁', h₁, ⟨d₁₁⟩, ⟨d₁₂⟩⟩ := HasType.app_inv exD_lawful d₁
  obtain ⟨τs, -, hty⟩ := HasType.con_inv exD_lawful d₁₁
  simp [DataSig.conTy, exSig, arrows, exField, exArity, Ty.subst] at hty
  obtain ⟨rfl, -, rfl, -⟩ := hty
  obtain ⟨τs₁₂, h₁₂, -⟩ := HasType.var_inv exD_lawful d₁₂
  obtain ⟨τs₂, h₂, -⟩ := HasType.var_inv exD_lawful d₂
  change (exD 0).Entails Q₁₂ (SConstr.tsubst _ givenC) at h₁₂
  change (exD 0).Entails Q₂ (SConstr.tsubst _ givenC) at h₂
  rw [givenC_tsubst] at h₁₂ h₂
  obtain ⟨hU, hc⟩ := ent_count h (by simp)
  simp only [SConstr.one_smul', SConstr.add_U, Finset.mem_union, not_or] at hU
  obtain ⟨hU₁, hU₂⟩ := hU
  obtain ⟨hU₁', hc₁⟩ := ent_count h₁ hU₁
  simp only [SConstr.one_smul', SConstr.add_U, Finset.mem_union, not_or] at hU₁'
  obtain ⟨-, hc₁₂⟩ := ent_count h₁₂ hU₁'.2
  obtain ⟨-, hc₂⟩ := ent_count h₂ hU₂
  simp only [SConstr.one_smul', SConstr.add_L, Multiset.count_add, givenC_L,
    Multiset.count_singleton_self] at hc hc₁ hc₁₂ hc₂
  omega

/-- `dithering = λx. if x then useC else 10` is rejected. -/
theorem dithering_rejected (π : Mult) (u : Fin 2 → Usage) (τ : Ty Unit 0) :
    IsEmpty (HasType exD exSig givenC exΓ u (dithering π) τ) := by
  refine ⟨fun d => ?_⟩
  obtain ⟨Q', π₀, τ₁, τ₂, h, -, ⟨d'⟩⟩ := HasType.lam_inv exD_lawful d
  obtain ⟨Q₁, Q₂, u₁, u₂, τs, h', -, halts⟩ := HasType.case_inv exD_lawful d'
  obtain ⟨d₀⟩ := halts ⟨0, by decide⟩
  obtain ⟨d₁⟩ := halts ⟨1, by decide⟩
  obtain ⟨τs₀, h₀, -⟩ := HasType.var_inv (x := 1) exD_lawful d₀
  obtain ⟨τs₁, h₁, -⟩ := HasType.con_inv exD_lawful d₁
  change (exD 0).Entails Q₂ (SConstr.tsubst _ givenC) at h₀
  rw [givenC_tsubst] at h₀
  obtain ⟨hU, -⟩ := ent_count h (by simp)
  obtain ⟨hU', -⟩ := ent_count h' hU
  simp only [SConstr.add_U, Finset.mem_union, not_or] at hU'
  obtain ⟨-, hc₀⟩ := ent_count h₀ hU'.2
  obtain ⟨-, hc₁⟩ := ent_count h₁ hU'.2
  simp only [givenC_L, Multiset.count_singleton_self, SConstr.zero_L,
    Multiset.count_zero] at hc₀ hc₁
  omega

/-- `notNeglecting` is also accepted by the inference algorithm of §6: constraint generation
(Figure 8) produces a wanted constraint `C` which the solver of Figure 9 (with the atomic solver
of Figure 10b) solves from the given `C`, consuming it entirely. -/
theorem notNeglecting_inferred :
    ∃ (u : Fin 2 → Usage) (W : Wanted (Atom Unit) 0), Gen exSig exΓ u notNeglecting intTy W ∧
      Solve exD (fun _ => simpleSolver cAtom) ∅ [] [cAtom] W [] := by
  have g₁₁ := Gen.var (sig := exSig) (Γ := exΓ) (x := 1) (σ := constScheme) 0 ![intTy, intTy] rfl
  have g₁₂ := Gen.var (sig := exSig) (Γ := exΓ) (x := 0) (σ := useCScheme) 0 Fin.elim0 rfl
  have g₂ := Gen.con (sig := exSig) (Γ := exΓ) 0 0 ⟨0, by decide⟩ Fin.elim0
  have e₁ : constScheme.τ.subst (instSub ![intTy, intTy]) =
      (.arr .one intTy (.arr .omega intTy intTy) : Ty Unit 0) := rfl
  have e₂ : useCScheme.τ.subst (instSub (Fin.elim0 : Fin 0 → Ty Unit 0)) = intTy := by
    simp only [useCScheme, intTy, Ty.subst]
    congr 1; funext l; exact l.elim0
  rw [e₁] at g₁₁
  rw [e₂] at g₁₂
  have g := Gen.app (Gen.app g₁₁ g₁₂) g₂
  have eQ₁ : constScheme.Q.tsubst (instSub ![intTy, intTy]) = 0 := by
    simp [constScheme, SConstr.tsubst]
  have eQ₂ : useCScheme.Q.tsubst (instSub (Fin.elim0 : Fin 0 → Ty Unit 0)) = givenC :=
    givenC_tsubst _
  rw [eQ₁, eQ₂, Wanted.one_smul, Wanted.smul_simple, smul_zero] at g
  refine ⟨_, _, g, .mult (.mult .empty (.atom ?_)) .empty⟩
  exact simpleSolver.oneL [] [] (by simp) (by simp)

/-- Hence, by the soundness of inference (Lemmas 6.4 and 6.5), `C ; Γ ⊢ const useC 10 : Int`
is derived from the output of the algorithm. -/
theorem notNeglecting_typed_by_inference :
    ∃ u : Fin 2 → Usage, Nonempty (HasType exD exSig givenC exΓ u notNeglecting intTy) := by
  obtain ⟨u, W, hG, hS⟩ := notNeglecting_inferred
  have h := (predLDomain_lawful ∅).infer_sound
    (fun k => simpleSolver_sound ((predLDomain_lawful ∅).lawful k) cAtom) hG
    (by simp) hS
  have e : (⟨∅, ((([] : List (Atom Unit 0)) : Multiset (Atom Unit 0)) +
      (([cAtom] : List (Atom Unit 0)) : Multiset (Atom Unit 0)))⟩ :
      SConstr (Atom Unit 0)) = givenC := by
    ext <;> simp [givenC]
  rw [e] at h
  exact ⟨u, h⟩

-- [PAPER ◀ END] §3.1, accepted and rejected examples

end Examples

end LQT
