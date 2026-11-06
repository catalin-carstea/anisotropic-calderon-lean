import Calderon.AngularShiftGraph

set_option autoImplicit false
noncomputable section
open Filter Set
open scoped Topology ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.AngularWeightedCore
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity
  SpectralWeightedGraph HarmonicDerivativeOperator HarmonicDerivativeBounds AngularShiftGraph

attribute [local irreducible] harmonicDerivative harmonicDerivativeAdjoint

lemma besselWeight_add_one (s : ℝ) (k : ℕ) :
    besselWeight (s+1) k = besselWeight s k * (1+(k:ℝ)) := by
  unfold besselWeight
  rw [Real.rpow_add (by positivity),Real.rpow_one]

lemma one_le_besselWeight (s : ℝ) (hs : 0 ≤ s) (k : ℕ) :
    1 ≤ besselWeight s k := by
  apply Real.one_le_rpow _ hs
  have hk : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
  linarith

lemma besselWeight_le_succ (s : ℝ) (hs : 0 ≤ s) (k : ℕ) :
    besselWeight s k ≤ besselWeight s (k+1) := by
  unfold besselWeight
  apply Real.rpow_le_rpow (by positivity) _ hs
  push_cast
  linarith

lemma besselWeight_succ_le (s : ℝ) (hs : 0 ≤ s) (k : ℕ) :
    besselWeight s (k+1) ≤ (2:ℝ)^s * besselWeight s k := by
  unfold besselWeight
  calc
    (1+((k+1:ℕ):ℝ))^s ≤ (2*(1+(k:ℝ)))^s := by
      apply Real.rpow_le_rpow (by positivity) _ hs
      push_cast
      nlinarith [show (0:ℝ) ≤ (k:ℝ) from Nat.cast_nonneg k]
    _ = _ := Real.mul_rpow (by norm_num) (by positivity)

lemma weighted_norm_harmonicDerivative_le (hF : SphereFischerInner) (s : ℝ) (hs : 0 ≤ s)
    (m : ℕ) (i : Fin 3) (q : harmonicSphereSubspace (m+1)) :
    besselWeight s m * ‖harmonicDerivative hF m i q‖ ≤
      2 * besselWeight (s+1) (m+1) * ‖q‖ := by
  have hd : ‖harmonicDerivative hF m i q‖ ≤ (2*((m:ℝ)+2))*‖q‖ :=
    (norm_harmonicDerivative_apply_le hF m i q).trans
      (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg q))
  calc
    _ ≤ besselWeight s (m+1) * ((2*((m:ℝ)+2))*‖q‖) :=
      mul_le_mul (besselWeight_le_succ s hs m) hd
        (norm_nonneg _) (le_of_lt (besselWeight_pos s (m+1)))
    _ = _ := by
      rw [besselWeight_add_one]
      push_cast
      ring

lemma weighted_norm_harmonicDerivativeAdjoint_le (hF : SphereFischerInner)
    (s : ℝ) (hs : 0 ≤ s) (m : ℕ) (i : Fin 3) (q : harmonicSphereSubspace m) :
    besselWeight s (m+1) * ‖harmonicDerivativeAdjoint hF m i q‖ ≤
      (2 * (2:ℝ)^s) * besselWeight (s+1) m * ‖q‖ := by
  calc
    _ ≤ ((2:ℝ)^s * besselWeight s m) * ((2*((m:ℝ)+1))*‖q‖) :=
      mul_le_mul (besselWeight_succ_le s hs m)
        (norm_harmonicDerivativeAdjoint_apply_le hF m i q)
        (norm_nonneg _)
        (mul_nonneg (Real.rpow_nonneg (show (0:ℝ) ≤ 2 by norm_num) s)
          (besselWeight_pos s m).le)
    _ = _ := by rw [besselWeight_add_one]; ring

lemma weighted_sq_harmonicDerivative_le (hF : SphereFischerInner) (s : ℝ) (hs : 0 ≤ s)
    (m : ℕ) (i : Fin 3) (q : harmonicSphereSubspace (m+1)) :
    besselWeight s m^2 * ‖harmonicDerivative hF m i q‖^2 ≤
      4 * (besselWeight (s+1) (m+1)^2 * ‖q‖^2) := by
  have h := pow_le_pow_left₀ (show 0 ≤ besselWeight s m *
      ‖harmonicDerivative hF m i q‖ from
        mul_nonneg (besselWeight_pos s m).le (norm_nonneg _))
    (weighted_norm_harmonicDerivative_le hF s hs m i q) 2
  simpa only [mul_pow,show (2:ℝ)^2 = 4 by norm_num,mul_assoc] using h

lemma weighted_sq_harmonicDerivativeAdjoint_le (hF : SphereFischerInner)
    (s : ℝ) (hs : 0 ≤ s) (m : ℕ) (i : Fin 3) (q : harmonicSphereSubspace m) :
    besselWeight s (m+1)^2 * ‖harmonicDerivativeAdjoint hF m i q‖^2 ≤
      (2 * (2:ℝ)^s)^2 * (besselWeight (s+1) m^2 * ‖q‖^2) := by
  have h := pow_le_pow_left₀ (show 0 ≤ besselWeight s (m+1) *
      ‖harmonicDerivativeAdjoint hF m i q‖ from
        mul_nonneg (besselWeight_pos s (m+1)).le (norm_nonneg _))
    (weighted_norm_harmonicDerivativeAdjoint_le hF s hs m i q) 2
  simpa only [mul_pow,mul_assoc] using h

/-- Exact nonnegative-order Bessel domain already defined by the genuine diagonal graph. -/
def hasSphereBesselWeight (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (s : ℝ) (u : SphereL2) : Prop := ∃ w : SphereL2, (u,w) ∈ sphereBesselGraph hO hD s

lemma hasSphereBesselWeight_iff_summable (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (s : ℝ) (u : SphereL2) :
    hasSphereBesselWeight hO hD s u ↔
      Summable (fun k : ℕ => besselWeight s k^2 * ‖sphereHarmonicCoordinate hO hD k u‖^2) := by
  simpa only [hasSphereBesselWeight,sphereBesselGraph,
    abs_of_pos (besselWeight_pos s _)] using
    exists_spectralGraph_iff_summable hO hD (besselWeight s) u

lemma summable_weighted_derivativeCoordinates (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3)
    (s : ℝ) (hs : 0 ≤ s) (u : SphereL2)
    (hu : hasSphereBesselWeight hO hD (s+1) u) :
    Summable (fun m : ℕ => besselWeight s m^2 *
      ‖harmonicDerivative hF m i (sphereHarmonicCoordinate hO hD (m+1) u)‖^2) := by
  have hb := (hasSphereBesselWeight_iff_summable hO hD (s+1) u).mp hu
  have ht := ((summable_nat_add_iff 1).mpr hb).mul_left (4:ℝ)
  exact Summable.of_nonneg_of_le (fun m => by positivity)
    (fun m => weighted_sq_harmonicDerivative_le hF s hs m i _) ht

lemma summable_weighted_raisingCoordinates (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3)
    (s : ℝ) (hs : 0 ≤ s) (u : SphereL2)
    (hu : hasSphereBesselWeight hO hD (s+1) u) :
    Summable (fun m : ℕ => besselWeight s (m+1)^2 *
      ‖harmonicDerivativeAdjoint hF m i (sphereHarmonicCoordinate hO hD m u)‖^2) := by
  have hb := (hasSphereBesselWeight_iff_summable hO hD (s+1) u).mp hu
  exact Summable.of_nonneg_of_le (fun m => by positivity)
    (fun m => weighted_sq_harmonicDerivativeAdjoint_le hF s hs m i _)
    (hb.mul_left ((2 * (2:ℝ)^s)^2))

/-- The derivative output is constructed, rather than assumed to lie in a desired domain. -/
lemma exists_sphereDerivativeGraph_hasWeight (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3)
    (s : ℝ) (hs : 0 ≤ s) (u : SphereL2)
    (hu : hasSphereBesselWeight hO hD (s+1) u) :
    ∃ du : SphereL2, (u,du) ∈ sphereDerivativeGraph hF hO hD i ∧
      hasSphereBesselWeight hO hD s du := by
  have hw := summable_weighted_derivativeCoordinates hF hO hD i s hs u hu
  have hd : Summable (fun m : ℕ =>
      ‖harmonicDerivative hF m i (sphereHarmonicCoordinate hO hD (m+1) u)‖^2) := by
    apply Summable.of_nonneg_of_le (fun m => sq_nonneg _) _ hw
    intro m
    have hweight := one_le_besselWeight s hs m
    have hsq : (1:ℝ) ≤ besselWeight s m^2 := by nlinarith
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hsq
      (sq_nonneg ‖harmonicDerivative hF m i (sphereHarmonicCoordinate hO hD (m+1) u)‖)
  obtain ⟨du,hdu⟩ := (exists_sphereDerivativeGraph_iff_summable hF hO hD i u).mpr hd
  refine ⟨du,hdu,(hasSphereBesselWeight_iff_summable hO hD s du).mpr ?_⟩
  have hcoord : ∀ m : ℕ, sphereHarmonicCoordinate hO hD m du =
      harmonicDerivative hF m i (sphereHarmonicCoordinate hO hD (m+1) u) := hdu
  simpa only [hcoord] using hw

lemma exists_sphereRaisingGraph_hasWeight (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3)
    (s : ℝ) (hs : 0 ≤ s) (u : SphereL2)
    (hu : hasSphereBesselWeight hO hD (s+1) u) :
    ∃ ru : SphereL2, (u,ru) ∈ sphereRaisingGraph hF hO hD i ∧
      hasSphereBesselWeight hO hD s ru := by
  have hw := summable_weighted_raisingCoordinates hF hO hD i s hs u hu
  have hr : Summable (fun m : ℕ =>
      ‖harmonicDerivativeAdjoint hF m i (sphereHarmonicCoordinate hO hD m u)‖^2) := by
    apply Summable.of_nonneg_of_le (fun m => sq_nonneg _) _ hw
    intro m
    have hweight := one_le_besselWeight s hs (m+1)
    have hsq : (1:ℝ) ≤ besselWeight s (m+1)^2 := by nlinarith
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hsq
      (sq_nonneg ‖harmonicDerivativeAdjoint hF m i (sphereHarmonicCoordinate hO hD m u)‖)
  obtain ⟨ru,hru⟩ := (exists_sphereRaisingGraph_iff_summable hF hO hD i u).mpr hr
  refine ⟨ru,hru,(hasSphereBesselWeight_iff_summable hO hD s ru).mpr ?_⟩
  apply (summable_nat_add_iff 1).mp
  have hcoord : ∀ m : ℕ, sphereHarmonicCoordinate hO hD (m+1) ru =
      harmonicDerivativeAdjoint hF m i (sphereHarmonicCoordinate hO hD m u) := hru.2
  simpa only [hcoord] using hw

lemma norm_sq_sphereBesselGraph_output (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (s : ℝ) (u w : SphereL2)
    (hw : (u,w) ∈ sphereBesselGraph hO hD s) :
    ‖w‖^2 = ∑' k : ℕ, besselWeight s k^2 * ‖sphereHarmonicCoordinate hO hD k u‖^2 := by
  simpa only [abs_of_pos (besselWeight_pos s _)] using
    norm_sq_spectralGraph_output hO hD (besselWeight s) u w hw

lemma norm_sq_weighted_derivative_le (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3)
    (s : ℝ) (hs : 0 ≤ s) (u wu du wdu : SphereL2)
    (hwu : (u,wu) ∈ sphereBesselGraph hO hD (s+1))
    (hdu : (u,du) ∈ sphereDerivativeGraph hF hO hD i)
    (hwdu : (du,wdu) ∈ sphereBesselGraph hO hD s) :
    ‖wdu‖^2 ≤ 4 * ‖wu‖^2 := by
  have hb := (hasSphereBesselWeight_iff_summable hO hD (s+1) u).mp ⟨wu,hwu⟩
  have ht := (summable_nat_add_iff 1).mpr hb
  have hd := summable_weighted_derivativeCoordinates hF hO hD i s hs u ⟨wu,hwu⟩
  have hbound := hd.tsum_le_tsum
    (fun m => weighted_sq_harmonicDerivative_le hF s hs m i
      (sphereHarmonicCoordinate hO hD (m+1) u)) (ht.mul_left (4:ℝ))
  have htail : (∑' m : ℕ, besselWeight (s+1) (m+1)^2 *
      ‖sphereHarmonicCoordinate hO hD (m+1) u‖^2) ≤
      ∑' m : ℕ, besselWeight (s+1) m^2 * ‖sphereHarmonicCoordinate hO hD m u‖^2 := by
    rw [hb.tsum_eq_zero_add]
    exact le_add_of_nonneg_left (by positivity)
  rw [norm_sq_sphereBesselGraph_output hO hD s du wdu hwdu,
    norm_sq_sphereBesselGraph_output hO hD (s+1) u wu hwu]
  have hcoord : ∀ m : ℕ, sphereHarmonicCoordinate hO hD m du =
      harmonicDerivative hF m i (sphereHarmonicCoordinate hO hD (m+1) u) := hdu
  simp_rw [hcoord]
  rw [tsum_mul_left] at hbound
  exact hbound.trans (mul_le_mul_of_nonneg_left htail (by norm_num))

lemma norm_sq_weighted_raising_le (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3)
    (s : ℝ) (hs : 0 ≤ s) (u wu ru wru : SphereL2)
    (hwu : (u,wu) ∈ sphereBesselGraph hO hD (s+1))
    (hru : (u,ru) ∈ sphereRaisingGraph hF hO hD i)
    (hwru : (ru,wru) ∈ sphereBesselGraph hO hD s) :
    ‖wru‖^2 ≤ (2 * (2:ℝ)^s)^2 * ‖wu‖^2 := by
  have hb := (hasSphereBesselWeight_iff_summable hO hD (s+1) u).mp ⟨wu,hwu⟩
  have hr := summable_weighted_raisingCoordinates hF hO hD i s hs u ⟨wu,hwu⟩
  have hbound := hr.tsum_le_tsum
    (fun m => weighted_sq_harmonicDerivativeAdjoint_le hF s hs m i
      (sphereHarmonicCoordinate hO hD m u)) (hb.mul_left ((2 * (2:ℝ)^s)^2))
  have hwr := (hasSphereBesselWeight_iff_summable hO hD s ru).mp ⟨wru,hwru⟩
  rw [norm_sq_sphereBesselGraph_output hO hD s ru wru hwru,
    norm_sq_sphereBesselGraph_output hO hD (s+1) u wu hwu,hwr.tsum_eq_zero_add]
  have hzero : sphereHarmonicCoordinate hO hD 0 ru = 0 := hru.1
  have hcoord : ∀ m : ℕ, sphereHarmonicCoordinate hO hD (m+1) ru =
      harmonicDerivativeAdjoint hF m i (sphereHarmonicCoordinate hO hD m u) := hru.2
  simp only [hzero,norm_zero,show (0:ℝ)^(2:ℕ) = 0 by norm_num,mul_zero,zero_add]
  simp_rw [hcoord]
  simpa only [tsum_mul_left] using hbound

/-- A genuine common domain defined by exact harmonic decay, with no mapping premise. -/
def sphereSmoothWeightedCore (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) :
    Set SphereL2 := {u | ∀ n : ℕ, hasSphereBesselWeight hO hD (n:ℝ) u}

lemma sphereSmoothWeightedCore_derivative (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3)
    (u : SphereL2) (hu : u ∈ sphereSmoothWeightedCore hO hD) :
    ∃ du : SphereL2, (u,du) ∈ sphereDerivativeGraph hF hO hD i ∧
      du ∈ sphereSmoothWeightedCore hO hD := by
  obtain ⟨du,hdu,_⟩ := exists_sphereDerivativeGraph_hasWeight hF hO hD i 0 (by norm_num) u
    (by simpa using hu 1)
  refine ⟨du,hdu,?_⟩
  intro n
  obtain ⟨dn,hdn,hn⟩ := exists_sphereDerivativeGraph_hasWeight hF hO hD i (n:ℝ)
    (Nat.cast_nonneg n) u (by simpa only [Nat.cast_add,Nat.cast_one] using hu (n+1))
  have he := sphereDerivativeGraph_output_unique hF hO hD i u du dn hdu hdn
  simpa only [he] using hn

lemma sphereSmoothWeightedCore_raising (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3)
    (u : SphereL2) (hu : u ∈ sphereSmoothWeightedCore hO hD) :
    ∃ ru : SphereL2, (u,ru) ∈ sphereRaisingGraph hF hO hD i ∧
      ru ∈ sphereSmoothWeightedCore hO hD := by
  obtain ⟨ru,hru,_⟩ := exists_sphereRaisingGraph_hasWeight hF hO hD i 0 (by norm_num) u
    (by simpa using hu 1)
  refine ⟨ru,hru,?_⟩
  intro n
  obtain ⟨rn,hrn,hn⟩ := exists_sphereRaisingGraph_hasWeight hF hO hD i (n:ℝ)
    (Nat.cast_nonneg n) u (by simpa only [Nat.cast_add,Nat.cast_one] using hu (n+1))
  have he := sphereRaisingGraph_output_unique hF hO hD i u ru rn hru hrn
  simpa only [he] using hn

lemma hasSphereBesselWeight_of_finite (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (s : ℝ) (u : SphereL2) (n : ℕ)
    (hu : ∀ k : ℕ, n ≤ k → sphereHarmonicCoordinate hO hD k u = 0) :
    hasSphereBesselWeight hO hD s u := by
  apply (hasSphereBesselWeight_iff_summable hO hD s u).mpr
  apply summable_of_ne_finset_zero (s := Finset.range n)
  intro k hk
  have hkn : n ≤ k := by simpa only [Finset.mem_range,not_lt] using hk
  rw [hu k hkn]
  simp

lemma sphereHarmonicPartialSum_mem_sphereSmoothWeightedCore
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (n : ℕ) (u : SphereL2) :
    sphereHarmonicPartialSum hO hD n u ∈ sphereSmoothWeightedCore hO hD := by
  intro s
  apply hasSphereBesselWeight_of_finite hO hD (s:ℝ) _ n
  intro k hk
  simp only [sphereHarmonicCoordinate_partialSum,if_neg (not_lt.mpr hk)]

/-- Finite common-core approximants converge in each exact Bessel graph. -/
lemma sphereBesselGraph_common_core_partialSum (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (s : ℝ) (u wu : SphereL2)
    (hwu : (u,wu) ∈ sphereBesselGraph hO hD s) (n : ℕ) :
    (sphereHarmonicPartialSum hO hD n u,sphereHarmonicPartialSum hO hD n wu) ∈
        sphereBesselGraph hO hD s ∧
      sphereHarmonicPartialSum hO hD n u ∈ sphereSmoothWeightedCore hO hD :=
  ⟨spectralGraph_partialSum hO hD (besselWeight s) (u,wu) hwu n,
    sphereHarmonicPartialSum_mem_sphereSmoothWeightedCore hO hD n u⟩

lemma dense_sphereSmoothWeightedCore (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) : Dense (sphereSmoothWeightedCore hO hD) := by
  intro u
  exact isClosed_closure.mem_of_tendsto (tendsto_sphereHarmonicPartialSum hO hD u)
    (Eventually.of_forall (fun n => subset_closure
      (sphereHarmonicPartialSum_mem_sphereSmoothWeightedCore hO hD n u)))

end OAI.AnisotropicCalderon.AngularWeightedCore
