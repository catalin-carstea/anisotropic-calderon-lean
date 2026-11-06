import Calderon.MetricSmooth
import Mathlib.Analysis.Distribution.TestFunction

/-! The full expansion precedes this actual LF test-space normalization. -/
set_option autoImplicit false
noncomputable section
open Set TopologicalSpace
open scoped ContDiff Distributions
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge

def metricVolumeTestMap (g : MatrixField) (hg : IsAdmissibleMetric g)
    (Ω : Opens R3) : 𝓓(Ω, ℝ) →L[ℝ] 𝓓(Ω, ℝ) :=
  TestFunction.bilinLeftCLM (ContinuousLinearMap.mul ℝ ℝ) (contDiff_vol g hg)

def metricVolumeTestInvMap (g : MatrixField) (hg : IsAdmissibleMetric g)
    (Ω : Opens R3) : 𝓓(Ω, ℝ) →L[ℝ] 𝓓(Ω, ℝ) :=
  TestFunction.bilinLeftCLM (ContinuousLinearMap.mul ℝ ℝ)
    ((contDiff_vol g hg).inv (fun x => ne_of_gt (vol_pos g hg x)))

@[simp] theorem metricVolumeTestMap_apply (g : MatrixField) (hg : IsAdmissibleMetric g)
    (Ω : Opens R3) (φ : 𝓓(Ω, ℝ)) (x : R3) :
    metricVolumeTestMap g hg Ω φ x = φ x * vol g x := rfl

@[simp] theorem metricVolumeTestInvMap_apply (g : MatrixField) (hg : IsAdmissibleMetric g)
    (Ω : Opens R3) (φ : 𝓓(Ω, ℝ)) (x : R3) :
    metricVolumeTestInvMap g hg Ω φ x = φ x / vol g x := by
  rfl

def metricVolumeTestEquiv (g : MatrixField) (hg : IsAdmissibleMetric g)
    (Ω : Opens R3) : 𝓓(Ω, ℝ) ≃L[ℝ] 𝓓(Ω, ℝ) where
  toLinearEquiv :=
    { toFun := metricVolumeTestMap g hg Ω
      invFun := metricVolumeTestInvMap g hg Ω
      map_add' := (metricVolumeTestMap g hg Ω).map_add
      map_smul' := (metricVolumeTestMap g hg Ω).map_smul
      left_inv := fun φ => by
        apply TestFunction.ext
        intro x
        simp [ne_of_gt (vol_pos g hg x)]
      right_inv := fun φ => by
        apply TestFunction.ext
        intro x
        simp [ne_of_gt (vol_pos g hg x)] }
  continuous_toFun := (metricVolumeTestMap g hg Ω).continuous
  continuous_invFun := (metricVolumeTestInvMap g hg Ω).continuous

theorem support_metricVolumeTestMap (g : MatrixField) (hg : IsAdmissibleMetric g)
    (Ω : Opens R3) (φ : 𝓓(Ω, ℝ)) :
    Function.support (metricVolumeTestMap g hg Ω φ) = Function.support φ := by
  ext x
  simp [Function.mem_support, ne_of_gt (vol_pos g hg x)]

theorem tsupport_metricVolumeTestMap (g : MatrixField) (hg : IsAdmissibleMetric g)
    (Ω : Opens R3) (φ : 𝓓(Ω, ℝ)) :
    tsupport (metricVolumeTestMap g hg Ω φ) = tsupport φ := by
  exact congrArg closure (support_metricVolumeTestMap g hg Ω φ)

theorem metricVolumeTestMap_eq_self_of_tsupport_exterior
    (g : MatrixField) (hg : IsAdmissibleMetric g) (Ω : Opens R3) (φ : 𝓓(Ω, ℝ))
    (hφ : tsupport φ ⊆ {x : R3 | 1 ≤ ‖x‖}) :
    metricVolumeTestMap g hg Ω φ = φ := by
  apply TestFunction.ext
  intro x
  by_cases hx : x ∈ tsupport φ
  · simp [vol_eq_one_of_exterior g hg x (hφ hx)]
  · have hzero : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
    simp [hzero]

theorem range_comp_metricVolumeTestEquiv
    (g : MatrixField) (hg : IsAdmissibleMetric g) (Ω : Opens R3)
    {X : Type*} (R : 𝓓(Ω, ℝ) → X) :
    Set.range (R ∘ metricVolumeTestEquiv g hg Ω) = Set.range R := by
  ext x
  constructor
  · rintro ⟨φ, rfl⟩
    exact ⟨metricVolumeTestEquiv g hg Ω φ, rfl⟩
  · rintro ⟨φ, rfl⟩
    refine ⟨(metricVolumeTestEquiv g hg Ω).symm φ, ?_⟩
    change R ((metricVolumeTestEquiv g hg Ω)
      ((metricVolumeTestEquiv g hg Ω).symm φ)) = R φ
    rw [ContinuousLinearEquiv.apply_symm_apply]

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.metricVolumeTestMap
#print axioms OAI.AnisotropicCalderon.ExteriorSource.metricVolumeTestInvMap
#print axioms OAI.AnisotropicCalderon.ExteriorSource.metricVolumeTestMap_apply
#print axioms OAI.AnisotropicCalderon.ExteriorSource.metricVolumeTestInvMap_apply
#print axioms OAI.AnisotropicCalderon.ExteriorSource.metricVolumeTestEquiv
#print axioms OAI.AnisotropicCalderon.ExteriorSource.support_metricVolumeTestMap
#print axioms OAI.AnisotropicCalderon.ExteriorSource.tsupport_metricVolumeTestMap
#print axioms OAI.AnisotropicCalderon.ExteriorSource.metricVolumeTestMap_eq_self_of_tsupport_exterior
#print axioms OAI.AnisotropicCalderon.ExteriorSource.range_comp_metricVolumeTestEquiv
