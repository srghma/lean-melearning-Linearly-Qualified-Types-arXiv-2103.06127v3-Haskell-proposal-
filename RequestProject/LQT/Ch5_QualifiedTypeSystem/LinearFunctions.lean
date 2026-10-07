module

public import RequestProject.LQT.Ch3_LinearConstraints.ExampleSetting
public import RequestProject.LQT.Ch5_QualifiedTypeSystem.TypingInv

/-!
# The *Linear functions* example of §5.2

Paper location: §5.2 "Typing rules", paragraph *Linear functions* ("If `f : a →ω b` and
`x : 1·q ⇒ a`, then calling `f x` would actually use `q` many times. We must make sure it is
impossible to derive `1·q ; f : a →ω b, x : 1·q ⇒ a ⊢ f x : b` ... On the other hand, it is
perfectly fine to have `1·q ; f : a →1 b, x : 1·q ⇒ a ⊢ f x : b`").

The example uses the setting of the §3.1 examples (`Ch3_LinearConstraints/ExampleSetting.lean`).

* `linearFun_typed`: with `f : Int →₁ Int`, `C ; useC, f ⊢ f useC : Int`;
* `unrestrictedFun_rejected`: with `f : Int →ω Int`, `f useC` is rejected at every type and usage.
-/

@[expose] public section

namespace LQT

namespace Examples

-- [PAPER ▶ START] §5.2, paragraph "Linear functions"

/-- The context `x : 1·C ⇒ Int` (index `0`), `f : Int →π Int` (index `1`). -/
def lfΓ (π : Mult) : Fin 2 → Scheme Unit 0 := ![useCScheme, ⟨0, 0, .arr π intTy intTy⟩]

/-- The application `f x`. -/
def fx : Tm exSig 0 2 := .app (.var 1) (.var 0)

/-- With a linear `f : Int →1 Int`: `1·C ; f : Int →1 Int, x : 1·C ⇒ Int ⊢ f x : Int`. -/
theorem linearFun_typed :
    ∃ u : Fin 2 → Usage, Nonempty (HasType exD exSig givenC (lfΓ .one) u fx intTy) := by
  have d₁ := HasType.var (D := exD) (sig := exSig) (Γ := lfΓ .one) (x := 1)
    (σ := ⟨0, 0, .arr .one intTy intTy⟩) 0 Fin.elim0 rfl
  have d₂ := HasType.var (D := exD) (sig := exSig) (Γ := lfΓ .one) (x := 0) (σ := useCScheme) 0
    Fin.elim0 rfl
  simp only [Ty.subst, intTy_subst] at d₁
  simp only [useCScheme, intTy_subst] at d₂
  refine ⟨_, ⟨.sub (.app d₁ d₂) ?_⟩⟩
  apply (exD_lawful 0).entails_of_eq
  simp [SConstr.tsubst]
  exact (givenC_tsubst _).symm

/-- With an unrestricted `f : Int →ω Int`, `f x` cannot be typed with the linear assumption
`1·C`, whatever the type and the usage of the context. -/
theorem unrestrictedFun_rejected (u : Fin 2 → Usage) (τ : Ty Unit 0) :
    IsEmpty (HasType exD exSig givenC (lfΓ .omega) u fx τ) := by
  refine ⟨fun d => ?_⟩
  obtain ⟨Q₁, Q₂, u₁, u₂, π, τ₁, h, ⟨d₁⟩, ⟨d₂⟩⟩ := HasType.app_inv exD_lawful d
  obtain ⟨τs, -, hty⟩ := HasType.var_inv exD_lawful d₁
  obtain ⟨τs₂, h₂, -⟩ := HasType.var_inv exD_lawful d₂
  simp [lfΓ, Ty.subst] at hty
  obtain ⟨rfl, -⟩ := hty
  change (exD 0).Entails Q₂ (SConstr.tsubst _ givenC) at h₂
  rw [givenC_tsubst] at h₂
  obtain ⟨hU, -⟩ := ent_count h (by simp)
  simp only [SConstr.add_U, SConstr.omega_smul_U, Finset.mem_union, Multiset.mem_toFinset,
    not_or] at hU
  obtain ⟨-, hU₂, hL₂⟩ := hU
  obtain ⟨-, hc⟩ := ent_count h₂ hU₂
  simp only [givenC_L, Multiset.count_singleton_self] at hc
  exact hL₂ (Multiset.count_pos.mp (by omega))

-- [PAPER ◀ END] §5.2, paragraph "Linear functions"

end Examples

end LQT
