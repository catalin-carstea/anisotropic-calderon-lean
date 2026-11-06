import Calderon.SupportedOperatorSection
import Calderon.WeightedIntegralCongruence

/-! Complete generic output assembly; see matching upfront expansion. -/
set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open SphereHarmonic
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
set_option Elab.async false

theorem exists_supported_operator_sections_of_pairing
    (U : Set R3) (hU : IsOpen U)
    (F G : R3 → SphereL2) (uF uG : R3 → Hi)
    (huF : ContDiff ℝ ∞ uF) (hcuF : HasCompactSupport uF)
    (huG : ContDiff ℝ ∞ uG) (hcuG : HasCompactSupport uG)
    (huFU : tsupport uF ⊆ U) (huGU : tsupport uG ⊆ U)
    (huFF : tsupport uF ⊆ tsupport F) (huGG : tsupport uG ⊆ tsupport G)
    (P Pd : R3 → Hi →L[ℝ] Half)
    (hP : ContDiffOn ℝ ∞ P U) (hPd : ContDiffOn ℝ ∞ Pd U)
    (lift : Half →L[ℝ] SphereL2)
    (K0 : SphereL2 →L[ℝ] Neg) (J : Half →L[ℝ] Neg)
    (hLift : ∀ v : Half, K0 (lift v) = J v)
    {rhs : R3 → Neg} (hGraph : ∀ y : R3, J (P y (uF y)) = rhs y)
    (weight : R3 → ℝ)
    (hInner : ∀ y : R3,
      ⟪lift (P y (uF y)), G y⟫_ℝ = ⟪F y, lift (Pd y (uG y))⟫_ℝ) :
    ∃ pF pdagG : R3 → SphereL2,
      ContDiff ℝ ∞ pF ∧ HasCompactSupport pF ∧ MemLp pF 2 (volume : Measure R3) ∧
      tsupport pF ⊆ tsupport F ∧
      ContDiff ℝ ∞ pdagG ∧ HasCompactSupport pdagG ∧ MemLp pdagG 2 (volume : Measure R3) ∧
      tsupport pdagG ⊆ tsupport G ∧
      (∀ y : R3, K0 (pF y) = rhs y) ∧
      (∀ y : R3, K0 (pdagG y) = J (Pd y (uG y))) ∧
      (∀ y : R3, ⟪pF y, G y⟫_ℝ = ⟪F y, pdagG y⟫_ℝ) ∧
      (∫ y : R3, weight y * ⟪pF y, G y⟫_ℝ) =
        ∫ y : R3, weight y * ⟪F y, pdagG y⟫_ℝ := by
  let pF : R3 → SphereL2 := fun y => lift (P y (uF y))
  let pdagG : R3 → SphereL2 := fun y => lift (Pd y (uG y))
  have hFSection := contDiff_comp_clm_apply_of_tsupport_subset
    U hU uF huF hcuF huFU P hP lift
  have hGSection := contDiff_comp_clm_apply_of_tsupport_subset
    U hU uG huG hcuG huGU Pd hPd lift
  refine ⟨pF,pdagG,hFSection.1,hFSection.2.1,hFSection.2.2.1,
    hFSection.2.2.2.trans huFF,
    hGSection.1,hGSection.2.1,hGSection.2.2.1,
    hGSection.2.2.2.trans huGG,?_,?_,hInner,?_⟩
  · intro y
    exact (hLift (P y (uF y))).trans (hGraph y)
  · intro y
    exact hLift (Pd y (uG y))
  · exact OAI.AnisotropicCalderon.integral_mul_eq_of_forall_eq
      (volume : Measure R3) weight
      (fun y : R3 => ⟪pF y, G y⟫_ℝ)
      (fun y : R3 => ⟪F y, pdagG y⟫_ℝ) hInner

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
