import Calderon.WeightedAngularConvergence
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.WeightedSpectralEnergy
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity PositiveSpectralCore
  SpectralWeightedGraph WeightedBaseSpectral WeightedAngularConvergence ReferenceDensityBounds

set_option backward.isDefEq.respectTransparency false in
lemma norm_harmonicCoordinate_sum_sq (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (s : Finset ℕ) (u : SphereL2) :
    ‖∑ k ∈ s, (sphereHarmonicCoordinate hO hD k u : SphereL2)‖^2 =
      ∑ k ∈ s, ‖sphereHarmonicCoordinate hO hD k u‖^2 := by
  change ‖∑ k ∈ s, (harmonicSphereSubspace k).subtypeₗᵢ
      ((sphereHarmonicDecomposition hO hD u) k)‖^2 =
    ∑ k ∈ s, ‖(sphereHarmonicDecomposition hO hD u) k‖^2
  exact (orthogonalFamily_harmonicSphereSubspaces hO).norm_sum
    (fun k : ℕ => (sphereHarmonicDecomposition hO hD u) k) s

lemma norm_spherePositivePartialSum_sq (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (n : ℕ) (u : SphereL2) :
    ‖spherePositivePartialSum hO hD n u‖^2 =
      ∑ k ∈ Finset.range n, ‖sphereHarmonicCoordinate hO hD (k+1) u‖^2 := by
  classical
  have hi : Set.InjOn (fun k : ℕ => k+1) (Finset.range n) :=
    fun a _ b _ h => Nat.add_right_cancel h
  have hs := norm_harmonicCoordinate_sum_sq hO hD
    ((Finset.range n).image (fun k : ℕ => k+1)) u
  rw [Finset.sum_image hi,Finset.sum_image hi] at hs
  simpa only [spherePositivePartialSum_apply,sphereHarmonicCoordinate_apply] using hs

/-- A finite sum over consecutive genuine output degrees, including j=0. -/
def sphereShiftPartialSum (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (j n : ℕ) (u : SphereL2) : SphereL2 :=
  ∑ k ∈ Finset.range n, (sphereHarmonicCoordinate hO hD (k+j) u : SphereL2)

lemma norm_sphereShiftPartialSum_sq (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (j n : ℕ) (u : SphereL2) :
    ‖sphereShiftPartialSum hO hD j n u‖^2 =
      ∑ k ∈ Finset.range n, ‖sphereHarmonicCoordinate hO hD (k+j) u‖^2 := by
  classical
  have hi : Set.InjOn (fun k : ℕ => k+j) (Finset.range n) :=
    fun a _ b _ h => Nat.add_right_cancel h
  have hs := norm_harmonicCoordinate_sum_sq hO hD
    ((Finset.range n).image (fun k : ℕ => k+j)) u
  rw [Finset.sum_image hi,Finset.sum_image hi] at hs
  exact hs

lemma norm_sphereShiftPartialSum_le (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (j n : ℕ) (u : SphereL2) :
    ‖sphereShiftPartialSum hO hD j n u‖ ≤ ‖u‖ := by
  classical
  have hi : Set.InjOn (fun k : ℕ => k+j) (Finset.range n) :=
    fun a _ b _ h => Nat.add_right_cancel h
  have hs := norm_sum_sphereHarmonicCoordinates_le hO hD
    ((Finset.range n).image (fun k : ℕ => k+j)) u
  rw [Finset.sum_image hi] at hs
  exact hs

lemma sphereShiftPartialSum_eq_sub (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (j n : ℕ) (u : SphereL2) :
    sphereShiftPartialSum hO hD j n u =
      sphereHarmonicPartialSum hO hD (j+n) u - sphereHarmonicPartialSum hO hD j u := by
  unfold sphereShiftPartialSum
  rw [sphereHarmonicPartialSum_apply,sphereHarmonicPartialSum_apply,
    Finset.sum_range_add,add_sub_cancel_left]
  apply Finset.sum_congr rfl
  intro k _
  change (sphereHarmonicCoordinate hO hD (k+j) u : SphereL2) =
    (sphereHarmonicCoordinate hO hD (j+k) u : SphereL2)
  exact congrArg (fun l : ℕ => (sphereHarmonicCoordinate hO hD l u : SphereL2))
    (Nat.add_comm k j)

lemma sphereHarmonicPartialSum_eq_zero_of_coordinates (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (j : ℕ) (u : SphereL2)
    (hu : ∀ k < j, sphereHarmonicCoordinate hO hD k u=0) :
    sphereHarmonicPartialSum hO hD j u=0 := by
  rw [sphereHarmonicPartialSum_apply]
  apply Finset.sum_eq_zero
  intro k hk
  simpa only [sphereHarmonicCoordinate_apply,Submodule.coe_zero] using
    congrArg (fun v : harmonicSphereSubspace k => (v : SphereL2))
      (hu k (Finset.mem_range.mp hk))

lemma tendsto_sphereShiftPartialSum (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (j : ℕ) (u : SphereL2)
    (hu : ∀ k < j, sphereHarmonicCoordinate hO hD k u=0) :
    Tendsto (fun n : ℕ => sphereShiftPartialSum hO hD j n u) atTop (𝓝 u) := by
  simp_rw [sphereShiftPartialSum_eq_sub,
    sphereHarmonicPartialSum_eq_zero_of_coordinates hO hD j u hu,sub_zero]
  simpa only [Nat.add_comm,Function.comp_def] using
    (tendsto_sphereHarmonicPartialSum hO hD u).comp (tendsto_add_atTop_nat j)

lemma continuous_sphereShiftPartialSum (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (j n : ℕ) (U : R3 → SphereL2) (hU : Continuous U) :
    Continuous (fun x => sphereShiftPartialSum hO hD j n (U x)) := by
  simp_rw [sphereShiftPartialSum_eq_sub]
  exact ((sphereHarmonicPartialSum hO hD (j+n)).continuous.comp hU).sub
    ((sphereHarmonicPartialSum hO hD j).continuous.comp hU)

lemma integrable_referenceBase_weighted_norm_sq (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (a : R3 → ℝ) (ha : Continuous a)
    (U : R3 → SphereL2) (hU : Continuous U) (hc : HasCompactSupport U) :
    Integrable (fun x => referenceDensityFamily g L (lam,x) * a x * ‖U x‖^2) := by
  have hnorm : HasCompactSupport (fun x => ‖U x‖^2) :=
    hc.comp_left (g := fun u : SphereL2 => ‖u‖^2) (by simp)
  have hprod : HasCompactSupport
      (fun x => referenceDensityFamily g L (lam,x) * a x * ‖U x‖^2) := hnorm.mul_left
  exact (((continuous_referenceBaseDensity g hg L lam).mul ha).mul
    (hU.norm.pow 2)).integrable_of_hasCompactSupport hprod

/-- Proved weighted-square convergence on actual compact fields and exact output degrees. -/
theorem tendsto_integral_sphereShiftPartialSum_sq
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (a : R3 → ℝ) (ha : Continuous a) (U : R3 → SphereL2) (hU : Continuous U)
    (hc : HasCompactSupport U) (j : ℕ)
    (hz : ∀ x k, k < j → sphereHarmonicCoordinate hO hD k (U x)=0) :
    Tendsto (fun n : ℕ => ∫ x, referenceDensityFamily g L (lam,x) * a x *
      ‖sphereShiftPartialSum hO hD j n (U x)‖^2) atTop
      (𝓝 (∫ x, referenceDensityFamily g L (lam,x) * a x * ‖U x‖^2)) := by
  have hnorm : HasCompactSupport (fun x => ‖U x‖^2) :=
    hc.comp_left (g := fun u : SphereL2 => ‖u‖^2) (by simp)
  have hprod : HasCompactSupport
      (fun x => |referenceDensityFamily g L (lam,x) * a x| * ‖U x‖^2) := hnorm.mul_left
  have hb : Integrable (fun x => |referenceDensityFamily g L (lam,x) * a x| * ‖U x‖^2) :=
    ((((continuous_referenceBaseDensity g hg L lam).mul ha).abs).mul
      (hU.norm.pow 2)).integrable_of_hasCompactSupport hprod
  apply tendsto_integral_of_dominated_convergence
    (fun x => |referenceDensityFamily g L (lam,x) * a x| * ‖U x‖^2)
  · intro n
    exact ((((continuous_referenceBaseDensity g hg L lam).mul ha).mul
      ((continuous_sphereShiftPartialSum hO hD j n U hU).norm.pow 2))).aestronglyMeasurable
  · exact hb
  · intro n
    apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs,
      abs_mul (referenceDensityFamily g L (lam,x) * a x)
        (‖sphereShiftPartialSum hO hD j n (U x)‖^2),
      abs_of_nonneg (sq_nonneg ‖sphereShiftPartialSum hO hD j n (U x)‖)]
    exact mul_le_mul_of_nonneg_left
      ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
        (norm_sphereShiftPartialSum_le hO hD j n (U x))) (abs_nonneg _)
  · apply Filter.Eventually.of_forall
    intro x
    exact ((tendsto_sphereShiftPartialSum hO hD j (U x) (hz x)).norm.pow 2).const_mul
      (referenceDensityFamily g L (lam,x) * a x)

end OAI.AnisotropicCalderon.WeightedSpectralEnergy
