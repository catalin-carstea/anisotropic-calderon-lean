import OAI.Analysis.AnisotropicCalderon.Defs
import TauCeti.Analysis.PDE.EnergyForm.Integrated.Basic

noncomputable section
open MeasureTheory
open scoped InnerProductSpace Gradient ContDiff

namespace OAI.AnisotropicCalderon.EnergyBridge

/-- The principal coefficient in the exact Cartesian energy convention. -/
def principalCoefficient (g : MatrixField) : MatrixField :=
  fun x => vol g x • (g x)⁻¹

/-- The Euclidean vector with the exact frozen differential coordinates. -/
def energyGradient (u : R3 → ℝ) (x : R3) : R3 :=
  WithLp.toLp 2 (d u x)

@[simp] theorem energyGradient_apply (u : R3 → ℝ) (x : R3) (i : Fin 3) :
    energyGradient u x i = d u x i := rfl

/-- The ordinary value/gradient jet accepted by Tau Ceti's integrated form. -/
def energyJet (u : R3 → ℝ) (x : R3) : ℝ × R3 := (u x, energyGradient u x)

/-- This comparison holds for the total derivative, including its default-zero cases. -/
theorem energyGradient_eq_gradient (u : R3 → ℝ) (x : R3) :
    energyGradient u x = gradient u x := by
  ext i
  have h := inner_gradient_left (𝕜 := ℝ) (f := u) (x := x)
    (y := EuclideanSpace.single i 1)
  simp only [EuclideanSpace.inner_single_right, RCLike.conj_to_real, one_mul] at h
  exact h.symm

/-- Exact pointwise agreement; no smoothness, symmetry, or integrability is assumed. -/
theorem energyIntegrand_energyJet_self (g : MatrixField) (u : R3 → ℝ) (x : R3) :
    TauCeti.PDE.energyIntegrand (principalCoefficient g x) 0 0
      (energyJet u x) (energyJet u x) =
      (∑ i, ∑ j, (g x)⁻¹ i j * d u x i * d u x j) * vol g x := by
  simp only [TauCeti.PDE.energyIntegrand_apply, energyJet, principalCoefficient,
    TauCeti.PDE.driftForm_apply, TauCeti.PDE.massForm_apply, inner_zero_left,
    zero_mul, add_zero]
  rw [TauCeti.PDE.matrixBilinearForm_smul_apply,
    TauCeti.PDE.matrixBilinearForm_apply]
  simp only [dotProduct, Matrix.mulVec, energyGradient_apply,
    Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The frozen energy is exactly Tau Ceti's integrated principal form. -/
theorem energy_eq_energyFormIntegral (g : MatrixField) (u : R3 → ℝ) :
    energy g u = TauCeti.PDE.energyFormIntegral
      ((volume : Measure R3).restrict B) (principalCoefficient g)
      (fun _ => 0) (fun _ => 0) (energyJet u) (energyJet u) := by
  unfold energy TauCeti.PDE.energyFormIntegral
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => (energyIntegrand_energyJet_self g u x).symm

/-- Smooth perturbations which vanish on the entire frozen exterior. -/
def smoothZeroExterior : Set (R3 → ℝ) :=
  {w | ContDiff ℝ ∞ w ∧ ∀ x : R3, 1 ≤ ‖x‖ → w x = 0}

/-- The frozen competitor class is exactly an affine translate of smooth zero-exterior functions. -/
theorem smoothCompetitors_eq_image (f : R3 → ℝ) (hf : ContDiff ℝ ∞ f) :
    {u | ContDiff ℝ ∞ u ∧ ∀ x : R3, 1 ≤ ‖x‖ → u x = f x} =
      (fun w => f + w) '' smoothZeroExterior := by
  ext u
  constructor
  · rintro ⟨hu, hex⟩
    refine ⟨u - f, ⟨hu.sub hf, ?_⟩, ?_⟩
    · intro x hx
      simp [hex x hx]
    · ext x
      simp
  · rintro ⟨w, ⟨hw, hex⟩, rfl⟩
    refine ⟨hf.add hw, ?_⟩
    intro x hx
    simp [hex x hx]

/-- An exact reindexing of the frozen infimum, with no existence of a minimizer asserted. -/
theorem minimalEnergy_eq_sInf_smoothZeroExterior (g : MatrixField) (f : R3 → ℝ)
    (hf : ContDiff ℝ ∞ f) :
    minimalEnergy g f = sInf ((fun w => energy g (f + w)) '' smoothZeroExterior) := by
  unfold minimalEnergy
  rw [smoothCompetitors_eq_image f hf, Set.image_image]

/-- The support closure may touch the sphere, but is confined to the closed ball. -/
theorem tsupport_subset_closedBall_of_smoothZeroExterior {w : R3 → ℝ}
    (hw : w ∈ smoothZeroExterior) : tsupport w ⊆ Metric.closedBall 0 1 := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  apply mem_closedBall_zero_iff.mpr
  by_contra h
  have hnorm : 1 ≤ ‖x‖ := (lt_of_not_ge h).le
  exact hx (hw.2 x hnorm)

/-- Every frozen smooth zero-exterior perturbation has compact support in ambient space. -/
theorem hasCompactSupport_of_smoothZeroExterior {w : R3 → ℝ}
    (hw : w ∈ smoothZeroExterior) : HasCompactSupport w := by
  exact (isCompact_closedBall (0 : R3) 1).of_isClosed_subset (isClosed_tsupport w)
    (tsupport_subset_closedBall_of_smoothZeroExterior hw)

end OAI.AnisotropicCalderon.EnergyBridge

#print axioms OAI.AnisotropicCalderon.EnergyBridge.energyGradient_eq_gradient
#print axioms OAI.AnisotropicCalderon.EnergyBridge.energyIntegrand_energyJet_self
#print axioms OAI.AnisotropicCalderon.EnergyBridge.energy_eq_energyFormIntegral
#print axioms OAI.AnisotropicCalderon.EnergyBridge.minimalEnergy_eq_sInf_smoothZeroExterior
#print axioms OAI.AnisotropicCalderon.EnergyBridge.hasCompactSupport_of_smoothZeroExterior
