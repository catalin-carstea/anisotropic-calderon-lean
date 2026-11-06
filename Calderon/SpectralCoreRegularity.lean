import Calderon.SphereHilbertDecomposition
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Topology.Algebra.Module.FiniteDimension

set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial Filter
open scoped ContDiff Topology ENNReal
namespace OAI.AnisotropicCalderon.SpectralCoreRegularity
open SphereHarmonic SphereHilbertDecomposition HarmonicSampling FischerConnectionTransport

def sphereHarmonicCoordinate (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (k : ℕ) : SphereL2 →L[ℝ] harmonicSphereSubspace k :=
  (lp.evalCLM ℝ (fun k : ℕ => harmonicSphereSubspace k) 2 k).comp
    (sphereHarmonicDecomposition hO hD).toContinuousLinearEquiv.toContinuousLinearMap

lemma sphereHarmonicCoordinate_apply (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (k : ℕ) (u : SphereL2) :
    sphereHarmonicCoordinate hO hD k u = sphereHarmonicDecomposition hO hD u k := rfl

lemma norm_sphereHarmonicCoordinate_le (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (k : ℕ) (u : SphereL2) :
    ‖sphereHarmonicCoordinate hO hD k u‖ ≤ ‖u‖ := by
  have h := lp.norm_apply_le_norm (show (2 : ℝ≥0∞) ≠ 0 by norm_num)
    (sphereHarmonicDecomposition hO hD u) k
  simpa only [sphereHarmonicCoordinate_apply, LinearIsometryEquiv.norm_map] using h

lemma sphereHarmonicCoordinate_subtype (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (k : ℕ) (v : harmonicSphereSubspace k) :
    sphereHarmonicCoordinate hO hD k (v : SphereL2) = v := by
  rw [sphereHarmonicCoordinate_apply, sphereHarmonicDecomposition_subtype]
  simp

def sphereHarmonicPartialSum (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (n : ℕ) : SphereL2 →L[ℝ] SphereL2 :=
  ∑ k ∈ Finset.range n, (harmonicSphereSubspace k).subtypeL.comp
    (sphereHarmonicCoordinate hO hD k)

lemma sphereHarmonicPartialSum_apply (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (n : ℕ) (u : SphereL2) :
    sphereHarmonicPartialSum hO hD n u =
      ∑ k ∈ Finset.range n, (sphereHarmonicDecomposition hO hD u k : SphereL2) := by
  simp [sphereHarmonicPartialSum, sphereHarmonicCoordinate_apply]

theorem tendsto_sphereHarmonicPartialSum (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (u : SphereL2) :
    Tendsto (fun n : ℕ => sphereHarmonicPartialSum hO hD n u) atTop (𝓝 u) := by
  simpa only [sphereHarmonicPartialSum_apply] using
    (hasSum_sphereHarmonicDecomposition hO hD u).tendsto_sum_nat

lemma contDiff_sphereHarmonicCoordinate (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (k : ℕ) (U : R3 → SphereL2)
    (hU : ContDiff ℝ ∞ U) :
    ContDiff ℝ ∞ (fun x => sphereHarmonicCoordinate hO hD k (U x)) :=
  (sphereHarmonicCoordinate hO hD k).contDiff.comp hU

lemma contDiff_sphereHarmonicPartialSum (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (n : ℕ) (U : R3 → SphereL2)
    (hU : ContDiff ℝ ∞ U) :
    ContDiff ℝ ∞ (fun x => sphereHarmonicPartialSum hO hD n (U x)) :=
  (sphereHarmonicPartialSum hO hD n).contDiff.comp hU

lemma fderiv_sphereHarmonicCoordinate (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (k : ℕ) (U : R3 → SphereL2) (x : R3)
    (hU : DifferentiableAt ℝ U x) :
    fderiv ℝ (fun y => sphereHarmonicCoordinate hO hD k (U y)) x =
      (sphereHarmonicCoordinate hO hD k).comp (fderiv ℝ U x) :=
  ((sphereHarmonicCoordinate hO hD k).hasFDerivAt.comp x hU.hasFDerivAt).fderiv

lemma fderiv_sphereHarmonicPartialSum (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (n : ℕ) (U : R3 → SphereL2) (x : R3)
    (hU : DifferentiableAt ℝ U x) :
    fderiv ℝ (fun y => sphereHarmonicPartialSum hO hD n (U y)) x =
      (sphereHarmonicPartialSum hO hD n).comp (fderiv ℝ U x) :=
  ((sphereHarmonicPartialSum hO hD n).hasFDerivAt.comp x hU.hasFDerivAt).fderiv

theorem tendsto_fderiv_sphereHarmonicPartialSum_apply (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (U : R3 → SphereL2) (x X : R3)
    (hU : DifferentiableAt ℝ U x) :
    Tendsto (fun n : ℕ => fderiv ℝ
      (fun y => sphereHarmonicPartialSum hO hD n (U y)) x X)
      atTop (𝓝 (fderiv ℝ U x X)) := by
  simp_rw [fderiv_sphereHarmonicPartialSum hO hD _ U x hU,
    ContinuousLinearMap.comp_apply]
  exact tendsto_sphereHarmonicPartialSum hO hD (fderiv ℝ U x X)

lemma sphereHarmonicCoordinate_eq_zero_of_eq_zero (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (k : ℕ) (U : R3 → SphereL2) (x : R3)
    (hU : U x = 0) : sphereHarmonicCoordinate hO hD k (U x) = 0 := by
  rw [hU, map_zero]

lemma sphereHarmonicPartialSum_eq_zero_of_eq_zero (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (n : ℕ) (U : R3 → SphereL2) (x : R3)
    (hU : U x = 0) : sphereHarmonicPartialSum hO hD n (U x) = 0 := by
  rw [hU, map_zero]

lemma hasCompactSupport_sphereHarmonicCoordinate (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (k : ℕ) (U : R3 → SphereL2)
    (hU : HasCompactSupport U) :
    HasCompactSupport (fun x => sphereHarmonicCoordinate hO hD k (U x)) :=
  hU.comp_left (map_zero (sphereHarmonicCoordinate hO hD k))

lemma hasCompactSupport_sphereHarmonicPartialSum (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (n : ℕ) (U : R3 → SphereL2)
    (hU : HasCompactSupport U) :
    HasCompactSupport (fun x => sphereHarmonicPartialSum hO hD n (U x)) :=
  hU.comp_left (map_zero (sphereHarmonicPartialSum hO hD n))

theorem exists_smooth_compact_coordinates_sphereHarmonicCoordinate
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (k : ℕ)
    (U : R3 → SphereL2) (hU : ContDiff ℝ ∞ U) (K : Set R3) (hK : IsCompact K)
    (hzero : ∀ x ∉ K, U x = 0) :
    ∃ n : ℕ, ∃ b : Fin n → MvPolynomial (Fin 3) ℝ, ∃ c : R3 → Fin n → ℝ,
      (∀ j, b j ∈ harmonicHomogeneous k) ∧ ContDiff ℝ ∞ c ∧ HasCompactSupport c ∧
      (∀ x, polynomialSphereL2 (finitePolynomialField b c x) =
        (sphereHarmonicCoordinate hO hD k (U x) : SphereL2)) ∧
      (∀ x ∉ K, c x = 0) := by
  classical
  letI := finiteDimensional_harmonicSphereSubspace k
  let B := Module.finBasis ℝ (harmonicSphereSubspace k)
  have hex : ∀ j, ∃ p : MvPolynomial (Fin 3) ℝ,
      p ∈ harmonicHomogeneous k ∧ polynomialSphereL2 p = (B j : SphereL2) := by
    intro j
    exact (B j).property
  choose b hb he using hex
  let c : R3 → Fin (Module.finrank ℝ (harmonicSphereSubspace k)) → ℝ :=
    fun x => B.equivFunL (sphereHarmonicCoordinate hO hD k (U x))
  have hc : ContDiff ℝ ∞ c :=
    B.equivFunL.contDiff.comp (contDiff_sphereHarmonicCoordinate hO hD k U hU)
  have hcz : ∀ x ∉ K, c x = 0 := by
    intro x hx
    change B.equivFunL (sphereHarmonicCoordinate hO hD k (U x)) = 0
    rw [hzero x hx, map_zero, map_zero]
  have hcomp : HasCompactSupport c := by
    apply hK.of_isClosed_subset (isClosed_tsupport _) ?_
    apply closure_minimal ?_ hK.isClosed
    intro x hx
    by_contra hnot
    exact hx (hcz x hnot)
  refine ⟨Module.finrank ℝ (harmonicSphereSubspace k), b, c, hb, hc, hcomp, ?_, hcz⟩
  intro x
  have hsum := congrArg (fun v : harmonicSphereSubspace k => (v : SphereL2))
    (B.sum_repr (sphereHarmonicCoordinate hO hD k (U x)))
  unfold finitePolynomialField
  rw [map_sum]
  have hterm (j) : polynomialSphereL2 (c x j • b j) = c x j • (B j : SphereL2) := by
    rw [map_smul, he j]
  simp_rw [hterm]
  simpa only [Submodule.coe_sum, Submodule.coe_smul, c, Module.Basis.equivFunL_apply,
    Module.Basis.equivFun_apply] using hsum

theorem exists_smooth_compact_polynomial_sphereHarmonicCoordinate
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (k : ℕ) (U : R3 → SphereL2)
    (hU : ContDiff ℝ ∞ U) (K : Set R3) (hK : IsCompact K)
    (hzero : ∀ x ∉ K, U x = 0) :
    ∃ n : ℕ, ∃ b : Fin n → MvPolynomial (Fin 3) ℝ, ∃ c : R3 → Fin n → ℝ,
      (∀ j, b j ∈ harmonicHomogeneous k) ∧ ContDiff ℝ ∞ c ∧ HasCompactSupport c ∧
      (∀ x, polynomialSphereL2 (finitePolynomialField b c x) =
        (sphereHarmonicCoordinate hO hD k (U x) : SphereL2)) ∧
      (∀ x ∉ K, finitePolynomialField b c x = 0) := by
  obtain ⟨n,b,c,hb,hc,hcompact,hrep,hcz⟩ :=
    exists_smooth_compact_coordinates_sphereHarmonicCoordinate hO hD k U hU K hK hzero
  refine ⟨n,b,c,hb,hc,hcompact,hrep,?_⟩
  intro x hx
  apply (polynomialSphereL2_eq_zero_iff hF k _
    (finitePolynomialField_harmonicHomogeneous k b hb c x)).mp
  rw [hrep x, hzero x hx, map_zero]
  rfl

end OAI.AnisotropicCalderon.SpectralCoreRegularity
