import Calderon.ActualFiniteHarmonicModelHorizontalProfileComparison
import Calderon.ActualNativeCoverSmoothPartition
import Mathlib.Algebra.Order.Chebyshev

set_option autoImplicit false
noncomputable section
open Set
open scoped BigOperators ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph SectionFiveErrorForms

private lemma norm_sq_sum_le_card_mul_sum_sq
    {ι : Type*} [Fintype ι] (v : ι → SphereL2) :
    ‖∑ i, v i‖ ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i, ‖v i‖ ^ 2 := by
  classical
  have hn := norm_sum_le (Finset.univ : Finset ι) v
  have hsq : ‖∑ i, v i‖ ^ 2 ≤ (∑ i, ‖v i‖) ^ 2 := by
    have h0 : 0 ≤ ∑ i, ‖v i‖ := Finset.sum_nonneg (fun i _ => norm_nonneg (v i))
    nlinarith only [hn, norm_nonneg (∑ i, v i), h0]
  exact hsq.trans (by
    simpa using
      (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => ‖v i‖)))

private lemma core_operator_sum_sq_le
    {ι : Type*} [Fintype ι]
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (T : Module.End ℝ (smoothCompactFiniteSphereCore hO hD))
    (G : ι → smoothCompactFiniteSphereCore hO hD) (x : R3) :
    ‖(T (∑ i, G i)).val x‖ ^ 2 ≤
      (Fintype.card ι : ℝ) * ∑ i, ‖(T (G i)).val x‖ ^ 2 := by
  classical
  simpa only [map_sum, Submodule.coe_sum, Finset.sum_apply] using
    norm_sq_sum_le_card_mul_sum_sq (fun i => (T (G i)).val x)

/-- The original four-term reference profile energy obeys the finite-sum bound. -/
theorem finiteCoreReferenceProfileEnergy_sum_le
    {ι : Type*} [Fintype ι]
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L q beta : ℝ) (hb : 0 ≤ beta)
    (G : ι → smoothCompactFiniteSphereCore hO hD) (x : R3) :
    finiteCoreReferenceProfileEnergy hO hD g hg L q beta (∑ i, G i) x ≤
      (Fintype.card ι : ℝ) * ∑ i, finiteCoreReferenceProfileEnergy hO hD g hg L q beta (G i) x := by
  classical
  let n : ℝ := Fintype.card ι
  let H := coreReferenceHorizontal hO hD g hg L q
  let W1 := coreWeightOperator hO hD (besselWeight 1)
  let WH := coreWeightOperator hO hD (besselWeight (1/2 : ℝ))
  let W3 := coreWeightOperator hO hD (besselWeight (3/2 : ℝ))
  have hT (T : Module.End ℝ (smoothCompactFiniteSphereCore hO hD)) :
      ‖(T (∑ i, G i)).val x‖ ^ 2 ≤ n * ∑ i, ‖(T (G i)).val x‖ ^ 2 :=
    core_operator_sum_sq_le hO hD T G x
  have hH : (∑ a : Fin 3, ‖(H a (∑ i, G i)).val x‖ ^ 2) ≤
      n * ∑ i, ∑ a : Fin 3, ‖(H a (G i)).val x‖ ^ 2 := by
    calc
      _ ≤ ∑ a : Fin 3, n * ∑ i, ‖(H a (G i)).val x‖ ^ 2 :=
        Finset.sum_le_sum (fun a _ => hT (H a))
      _ = _ := by rw [← Finset.mul_sum, Finset.sum_comm]
  have hWH : (∑ a : Fin 3, ‖(WH (H a (∑ i, G i))).val x‖ ^ 2) ≤
      n * ∑ i, ∑ a : Fin 3, ‖(WH (H a (G i))).val x‖ ^ 2 := by
    calc
      _ ≤ ∑ a : Fin 3, n * ∑ i, ‖(WH (H a (G i))).val x‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro a _
        simpa only [Module.End.mul_apply] using hT (WH * H a)
      _ = _ := by rw [← Finset.mul_sum, Finset.sum_comm]
  change (∑ a : Fin 3, ‖(H a (∑ i, G i)).val x‖ ^ 2) +
      beta ^ 2 * ‖(W1 (∑ i, G i)).val x‖ ^ 2 +
      beta⁻¹ * (∑ a : Fin 3, ‖(WH (H a (∑ i, G i))).val x‖ ^ 2) +
      beta * ‖(W3 (∑ i, G i)).val x‖ ^ 2 ≤
    n * ∑ i, ((∑ a : Fin 3, ‖(H a (G i)).val x‖ ^ 2) +
      beta ^ 2 * ‖(W1 (G i)).val x‖ ^ 2 +
      beta⁻¹ * (∑ a : Fin 3, ‖(WH (H a (G i))).val x‖ ^ 2) +
      beta * ‖(W3 (G i)).val x‖ ^ 2)
  calc
    _ ≤ (n * ∑ i, ∑ a : Fin 3, ‖(H a (G i)).val x‖ ^ 2) +
        beta ^ 2 * (n * ∑ i, ‖(W1 (G i)).val x‖ ^ 2) +
        beta⁻¹ * (n * ∑ i, ∑ a : Fin 3, ‖(WH (H a (G i))).val x‖ ^ 2) +
        beta * (n * ∑ i, ‖(W3 (G i)).val x‖ ^ 2) :=
      add_le_add (add_le_add (add_le_add hH
        (mul_le_mul_of_nonneg_left (hT W1) (sq_nonneg beta)))
        (mul_le_mul_of_nonneg_left hWH (inv_nonneg.mpr hb)))
        (mul_le_mul_of_nonneg_left (hT W3) hb)
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      ring

/-- A scalar partition is first an equality of the global finite-core inputs. -/
theorem finiteCoreReferenceProfileEnergy_partition_le
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L q beta : ℝ) (hb : 0 ≤ beta)
    (N : ℕ) (theta : Fin N → R3 → ℝ) (hTheta : ∀ i, ContDiff ℝ ∞ (theta i))
    (hPartition : ∀ y ∈ MixedKernelConstructionTask.cylinder, ∑ i, theta i y = 1)
    (F : smoothCompactFiniteSphereCore hO hD)
    (hSupport : tsupport F.val ⊆ MixedKernelConstructionTask.cylinder) (x : R3) :
    finiteCoreReferenceProfileEnergy hO hD g hg L q beta F x ≤
      (N : ℝ) * ∑ i, finiteCoreReferenceProfileEnergy hO hD g hg L q beta
        (coreScalar hO hD (theta i) (hTheta i) F) x := by
  classical
  have hCore : F = ∑ i, coreScalar hO hD (theta i) (hTheta i) F := by
    apply Subtype.ext
    funext y
    simp only [Submodule.coe_sum, Finset.sum_apply]
    change F.val y = ∑ i, theta i y • F.val y
    rw [← Finset.sum_smul]
    by_cases hy : y ∈ MixedKernelConstructionTask.cylinder
    · rw [hPartition y hy, one_smul]
    · have hz : F.val y = 0 := image_eq_zero_of_notMem_tsupport
        (fun h => hy (hSupport h))
      simp only [hz, smul_zero]
  have h := finiteCoreReferenceProfileEnergy_sum_le hO hD g hg L q beta hb
    (fun i : Fin N => coreScalar hO hD (theta i) (hTheta i) F) x
  rw [← hCore] at h
  simpa only [Fintype.card_fin] using h

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
