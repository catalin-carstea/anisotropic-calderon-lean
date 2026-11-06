import Calderon.SpectralCoreRegularity

set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial Filter
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.PositiveSpectralCore
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity

lemma sphereMean_sphereHarmonicCoordinate_zero (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (u : SphereL2) :
    sphereMean (sphereHarmonicCoordinate hO hD 0 u : SphereL2) = sphereMean u := by
  let e : harmonicSphereSubspace 0 :=
    ⟨polynomialSphereL2 (C 1), polynomialSphereL2_mem 0 (C 1) (C_harmonicHomogeneous 1)⟩
  have hi := (sphereHarmonicDecomposition hO hD).inner_map_map (e : SphereL2) u
  rw [sphereHarmonicDecomposition_subtype hO hD 0 e, lp.inner_single_left] at hi
  exact hi

theorem sphereHarmonicCoordinate_zero_eq_mean (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (u : SphereL2) :
    (sphereHarmonicCoordinate hO hD 0 u : SphereL2) =
      sphereMean u • polynomialSphereL2 (C 1) := by
  have hm := sphereHarmonicDecomposition_zero_mem_constants hO hD u
  obtain ⟨r,hr⟩ := Submodule.mem_span_singleton.mp hm
  have hmean := sphereMean_sphereHarmonicCoordinate_zero hO hD u
  change sphereMean (sphereHarmonicDecomposition hO hD u 0 : SphereL2) = sphereMean u at hmean
  rw [← hr, map_smul, sphereMean_constant_one] at hmean
  simp only [smul_eq_mul, mul_one] at hmean
  change (sphereHarmonicDecomposition hO hD u 0 : SphereL2) = _
  rw [← hr, hmean]

lemma sphereHarmonicCoordinate_zero_eq_zero_iff (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (u : SphereL2) :
    sphereHarmonicCoordinate hO hD 0 u = 0 ↔ sphereMean u = 0 := by
  constructor
  · intro hz
    have hm := sphereMean_sphereHarmonicCoordinate_zero hO hD u
    rw [hz] at hm
    simpa using hm.symm
  · intro hm
    apply Subtype.ext
    simpa [hm] using sphereHarmonicCoordinate_zero_eq_mean hO hD u

def spherePositiveProjection (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) : SphereL2 →L[ℝ] SphereL2 :=
  ContinuousLinearMap.id ℝ SphereL2 - (harmonicSphereSubspace 0).subtypeL.comp
    (sphereHarmonicCoordinate hO hD 0)

lemma spherePositiveProjection_apply (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (u : SphereL2) :
    spherePositiveProjection hO hD u = u - sphereMean u • polynomialSphereL2 (C 1) := by
  simp [spherePositiveProjection, sphereHarmonicCoordinate_zero_eq_mean]

lemma spherePositiveProjection_mem_meanZero (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (u : SphereL2) :
    spherePositiveProjection hO hD u ∈ meanZeroSphere := by
  change sphereMean (spherePositiveProjection hO hD u) = 0
  rw [spherePositiveProjection_apply, map_sub, map_smul, sphereMean_constant_one]
  simp

lemma spherePositiveProjection_eq_self (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (u : SphereL2) (hu : sphereMean u = 0) :
    spherePositiveProjection hO hD u = u := by
  simp [spherePositiveProjection_apply, hu]

lemma spherePositiveProjection_idempotent (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (u : SphereL2) :
    spherePositiveProjection hO hD (spherePositiveProjection hO hD u) =
      spherePositiveProjection hO hD u :=
  spherePositiveProjection_eq_self hO hD _ (spherePositiveProjection_mem_meanZero hO hD u)

lemma spherePositiveProjection_constant_one (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) :
    spherePositiveProjection hO hD (polynomialSphereL2 (C 1)) = 0 := by
  rw [spherePositiveProjection_apply, sphereMean_constant_one, one_smul, sub_self]

def spherePositivePartialSum (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (n : ℕ) : SphereL2 →L[ℝ] SphereL2 :=
  ∑ k ∈ Finset.range n, (harmonicSphereSubspace (k+1)).subtypeL.comp
    (sphereHarmonicCoordinate hO hD (k+1))

lemma spherePositivePartialSum_apply (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (n : ℕ) (u : SphereL2) :
    spherePositivePartialSum hO hD n u =
      ∑ k ∈ Finset.range n, (sphereHarmonicDecomposition hO hD u (k+1) : SphereL2) := by
  simp [spherePositivePartialSum, sphereHarmonicCoordinate_apply]

lemma spherePositivePartialSum_eq_sub (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (n : ℕ) (u : SphereL2) :
    spherePositivePartialSum hO hD n u = sphereHarmonicPartialSum hO hD (n+1) u -
      (sphereHarmonicCoordinate hO hD 0 u : SphereL2) := by
  rw [spherePositivePartialSum_apply, sphereHarmonicPartialSum_apply, Finset.sum_range_succ']
  simp only [sphereHarmonicCoordinate_apply]
  abel

lemma spherePositivePartialSum_mem_meanZero (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (n : ℕ) (u : SphereL2) :
    spherePositivePartialSum hO hD n u ∈ meanZeroSphere := by
  rw [spherePositivePartialSum_apply]
  apply meanZeroSphere.sum_mem
  intro k hk
  exact harmonicSphereSubspace_le_meanZero hO (k+1) (by omega)
    (sphereHarmonicDecomposition hO hD u (k+1)).property

theorem tendsto_spherePositivePartialSum (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (u : SphereL2) :
    Tendsto (fun n : ℕ => spherePositivePartialSum hO hD n u) atTop
      (𝓝 (spherePositiveProjection hO hD u)) := by
  have ht := (tendsto_sphereHarmonicPartialSum hO hD u).comp (tendsto_add_atTop_nat 1)
  have hs := ht.sub_const (sphereHarmonicCoordinate hO hD 0 u : SphereL2)
  simpa only [spherePositivePartialSum_eq_sub, spherePositiveProjection_apply,
    sphereHarmonicCoordinate_zero_eq_mean, Function.comp_def] using hs

theorem tendsto_spherePositivePartialSum_of_meanZero (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (u : SphereL2) (hu : sphereMean u = 0) :
    Tendsto (fun n : ℕ => spherePositivePartialSum hO hD n u) atTop (𝓝 u) := by
  simpa only [spherePositiveProjection_eq_self hO hD u hu] using
    tendsto_spherePositivePartialSum hO hD u

lemma contDiff_spherePositivePartialSum (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (n : ℕ) (U : R3 → SphereL2)
    (hU : ContDiff ℝ ∞ U) :
    ContDiff ℝ ∞ (fun x => spherePositivePartialSum hO hD n (U x)) :=
  (spherePositivePartialSum hO hD n).contDiff.comp hU

lemma hasCompactSupport_spherePositivePartialSum (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (n : ℕ) (U : R3 → SphereL2)
    (hU : HasCompactSupport U) :
    HasCompactSupport (fun x => spherePositivePartialSum hO hD n (U x)) :=
  hU.comp_left (map_zero (spherePositivePartialSum hO hD n))

lemma spherePositivePartialSum_eq_zero_of_eq_zero (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (n : ℕ) (U : R3 → SphereL2) (x : R3) (hU : U x = 0) :
    spherePositivePartialSum hO hD n (U x) = 0 := by
  rw [hU, map_zero]

lemma fderiv_spherePositivePartialSum (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (n : ℕ) (U : R3 → SphereL2) (x : R3)
    (hU : DifferentiableAt ℝ U x) :
    fderiv ℝ (fun y => spherePositivePartialSum hO hD n (U y)) x =
      (spherePositivePartialSum hO hD n).comp (fderiv ℝ U x) :=
  ((spherePositivePartialSum hO hD n).hasFDerivAt.comp x hU.hasFDerivAt).fderiv

lemma sphereMean_fderiv_eq_zero (U : R3 → SphereL2) (x X : R3)
    (hU : DifferentiableAt ℝ U x) (hmean : ∀ y, sphereMean (U y) = 0) :
    sphereMean (fderiv ℝ U x X) = 0 := by
  have hfun : (fun y => sphereMean (U y)) = (fun _ : R3 => (0 : ℝ)) := funext hmean
  have hf := (sphereMean.hasFDerivAt.comp x hU.hasFDerivAt).fderiv
  change fderiv ℝ (fun y => sphereMean (U y)) x = sphereMean.comp (fderiv ℝ U x) at hf
  rw [hfun] at hf
  have hz : fderiv ℝ (fun _ : R3 => (0 : ℝ)) x = 0 := (hasFDerivAt_const (0 : ℝ) x).fderiv
  rw [hz] at hf
  have hv := congrArg (fun T : R3 →L[ℝ] ℝ => T X) hf
  simpa using hv.symm

theorem tendsto_fderiv_spherePositivePartialSum_apply (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (U : R3 → SphereL2) (x X : R3)
    (hU : DifferentiableAt ℝ U x) (hmean : ∀ y, sphereMean (U y) = 0) :
    Tendsto (fun n : ℕ => fderiv ℝ
      (fun y => spherePositivePartialSum hO hD n (U y)) x X)
      atTop (𝓝 (fderiv ℝ U x X)) := by
  simp_rw [fderiv_spherePositivePartialSum hO hD _ U x hU,
    ContinuousLinearMap.comp_apply]
  exact tendsto_spherePositivePartialSum_of_meanZero hO hD _
    (sphereMean_fderiv_eq_zero U x X hU hmean)

end OAI.AnisotropicCalderon.PositiveSpectralCore
