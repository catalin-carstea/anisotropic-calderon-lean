import Calderon.TauMetricDirichlet
import Calderon.TauAffineBallData
noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace ContDiff
namespace OAI.AnisotropicCalderon.EnergyBridge

/-- Actual weak harmonic extensions for frozen admissible metrics. -/
def metricDirichletSolution (g : MatrixField) (hg : IsAdmissibleMetric g) (f : SmoothData) : BallH1 :=
  affineDirichletSolution g f (memLp_metricEnergyIntegrand g hg) (isCoercive_metricEnergyForm g hg)

/-- The actual variational boundary pairing on all smooth data. -/
def smoothBoundaryPairing (g : MatrixField) (hg : IsAdmissibleMetric g) (f h : SmoothData) : ℝ :=
  TauCeti.PDE.energyFormH1 (principalCoefficient g) (fun _ : R3 => (0 : R3)) (fun _ : R3 => (0 : ℝ))
    (metricDirichletSolution g hg f) (metricDirichletSolution g hg h)

/-- Frozen minimal energy is the diagonal of this genuine pairing. -/
theorem smoothBoundaryPairing_self (hzero : SmoothBoundaryZeroClosure)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (f : SmoothData) :
    smoothBoundaryPairing g hg f f = minimalEnergy g f.1 :=
  (minimalEnergy_eq_affineDirichletSolution_energy hzero g f
    (memLp_metricEnergyIntegrand g hg) (isCoercive_metricEnergyForm g hg)
    (metricEnergy_coefficient_isSymm_ae g hg)).symm

/-- Real polarization is proved on the actual metric harmonic extensions. -/
theorem two_mul_smoothBoundaryPairing (hzero : SmoothBoundaryZeroClosure)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (f h : SmoothData) :
    2 * smoothBoundaryPairing g hg f h =
      minimalEnergy g (f.1 + h.1) - minimalEnergy g f.1 - minimalEnergy g h.1 := by
  rw [← smoothBoundaryPairing_self hzero g hg ⟨f.1 + h.1, f.2.add h.2⟩,
    ← smoothBoundaryPairing_self hzero g hg f, ← smoothBoundaryPairing_self hzero g hg h]
  unfold smoothBoundaryPairing metricDirichletSolution
  rw [affineDirichletSolution_add]
  rw [TauCeti.PDE.energyFormH1_add_left (memLp_metricEnergyIntegrand g hg),
    TauCeti.PDE.energyFormH1_add_right (memLp_metricEnergyIntegrand g hg),
    TauCeti.PDE.energyFormH1_add_right (memLp_metricEnergyIntegrand g hg)]
  have hcomm := TauCeti.PDE.energyFormH1_comm_of_isSymm_ae
    (mu := (volume : Measure R3)) (Omega := ballOpens) (a := principalCoefficient g)
    (c := fun _ : R3 => (0 : ℝ)) (metricEnergy_coefficient_isSymm_ae g hg)
    (affineDirichletSolution g h (memLp_metricEnergyIntegrand g hg) (isCoercive_metricEnergyForm g hg))
    (affineDirichletSolution g f (memLp_metricEnergyIntegrand g hg) (isCoercive_metricEnergyForm g hg))
  simp only [Pi.zero_def] at hcomm
  rw [hcomm]
  ring

/-- The exact frozen equal-energy data implies equality of genuine mixed boundary pairings. -/
theorem smoothBoundaryPairing_eq_of_minimalEnergy_eq (hzero : SmoothBoundaryZeroClosure)
    (g₁ g₂ : MatrixField) (hg₁ : IsAdmissibleMetric g₁) (hg₂ : IsAdmissibleMetric g₂)
    (hΛ : ∀ f : R3 → ℝ, ContDiff ℝ ∞ f → minimalEnergy g₁ f = minimalEnergy g₂ f)
    (f h : SmoothData) : smoothBoundaryPairing g₁ hg₁ f h = smoothBoundaryPairing g₂ hg₂ f h := by
  have h₁ := two_mul_smoothBoundaryPairing hzero g₁ hg₁ f h
  have h₂ := two_mul_smoothBoundaryPairing hzero g₂ hg₂ f h
  rw [hΛ (f.1 + h.1) (f.2.add h.2), hΛ f.1 f.2, hΛ h.1 h.2] at h₁
  linarith

/-- This actual Sobolev harmonic extension depends only on the ordinary sphere boundary value. -/
theorem metricDirichletSolution_eq_of_boundary_eq (hzero : SmoothBoundaryZeroClosure)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (f h : SmoothData)
    (heq : ∀ x : R3, ‖x‖ = 1 → f.1 x = h.1 x) :
    metricDirichletSolution g hg f = metricDirichletSolution g hg h := by
  have hd : smoothSobolev f - smoothSobolev h ∈ TauCeti.w1p0Submodule volume ballOpens 2 := by
    rw [← smoothSobolev_sub]
    apply hzero ⟨f.1 - h.1, f.2.sub h.2⟩
    intro x hx
    simp [heq x hx]
  have hc := (affineDirichletCorrection g h (memLp_metricEnergyIntegrand g hg)
    (isCoercive_metricEnergyForm g hg)).2
  apply Eq.symm
  apply eq_affineDirichletSolution g (memLp_metricEnergyIntegrand g hg) (isCoercive_metricEnergyForm g hg) f
  · have he : metricDirichletSolution g hg h - smoothSobolev f =
        (affineDirichletCorrection g h (memLp_metricEnergyIntegrand g hg)
          (isCoercive_metricEnergyForm g hg) : BallH1) - (smoothSobolev f - smoothSobolev h) := by
      unfold metricDirichletSolution affineDirichletSolution tauAffineSolution affineDirichletCorrection
      abel
    rw [he]
    exact (TauCeti.w1p0Submodule volume ballOpens 2).sub_mem hc hd
  · exact energyForm_affineDirichletSolution_zero g h (memLp_metricEnergyIntegrand g hg)
      (isCoercive_metricEnergyForm g hg)

end OAI.AnisotropicCalderon.EnergyBridge
#print axioms OAI.AnisotropicCalderon.EnergyBridge.smoothBoundaryPairing_eq_of_minimalEnergy_eq
#print axioms OAI.AnisotropicCalderon.EnergyBridge.metricDirichletSolution_eq_of_boundary_eq
