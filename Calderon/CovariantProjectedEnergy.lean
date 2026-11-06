import Calderon.CovariantHarmonicEnergy

set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial
open scoped ContDiff InnerProductSpace Topology
namespace OAI.AnisotropicCalderon.CovariantProjectedEnergy
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity
  CovariantHarmonicEnergy FischerConnectionTransport FiniteProfileNormComparison
  ReferenceDensityBounds RadiusProfile

/-- Coordinates and covariant energy equality are derived for the actual projection. -/
theorem exists_coordinates_covariant_sphereHarmonicCoordinate
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (lam δ R L : ℝ) (p k : ℕ)
    (U : R3 → SphereL2) (hU : ContDiff ℝ ∞ U)
    (K : Set R3) (hK : IsCompact K) (hzero : ∀ x ∉ K, U x = 0) :
    ∃ n : ℕ, ∃ b : Fin n → MvPolynomial (Fin 3) ℝ, ∃ c : R3 → Fin n → ℝ,
      (∀ j, b j ∈ harmonicHomogeneous k) ∧ ContDiff ℝ ∞ c ∧ HasCompactSupport c ∧
      (∀ x ∉ K, c x = 0) ∧
      (∀ x, polynomialSphereL2 (finitePolynomialField b c x) =
        (sphereHarmonicCoordinate hO hD k (U x) : SphereL2)) ∧
      (∀ x X, polynomialSphereL2 (referenceCovariantPolynomialDerivative g L lam b c x X) =
        (referenceHarmonicCovariantDerivative g L lam k
          (fun y => sphereHarmonicCoordinate hO hD k (U y)) x X : SphereL2)) ∧
      (∀ x, referenceHarmonicModeEnergyDensity g lam δ R L p k
        (fun y => sphereHarmonicCoordinate hO hD k (U y)) x =
          referenceProfileModeEnergyDensity g hg lam δ R L p k b c x) ∧
      referenceHarmonicModeEnergy g lam δ R L p k
        (fun y => sphereHarmonicCoordinate hO hD k (U y)) =
          referenceProfileModeEnergy g hg lam δ R L p k b c := by
  obtain ⟨n,b,c,hb,hc,hcompact,hrep,hcz⟩ :=
    exists_smooth_compact_coordinates_sphereHarmonicCoordinate hO hD k U hU K hK hzero
  have hproj := contDiff_sphereHarmonicCoordinate hO hD k U hU
  refine ⟨n,b,c,hb,hc,hcompact,hcz,hrep,?_,?_,?_⟩
  · intro x X
    exact polynomialSphereL2_referenceCovariantDerivative g hg L lam k b hb c _ hc hproj hrep x X
  · intro x
    exact referenceHarmonicModeEnergyDensity_eq_polynomial g hg lam δ R L p k b hb c _ hc hproj hrep x
  · exact referenceHarmonicModeEnergy_eq_polynomial g hg lam δ R L p k b hb c _ hc hproj hrep

theorem integrable_referenceHarmonicModeEnergy_projection
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (lam δ R L : ℝ) (p k : ℕ)
    (hδ : 0 < δ) (hR : 0 < R) (hL : 0 < L) (hp : 1 ≤ p) (hk : 1 ≤ k)
    (U : R3 → SphereL2) (hU : ContDiff ℝ ∞ U)
    (K : Set R3) (hK : IsCompact K) (hzero : ∀ x ∉ K, U x = 0) :
    Integrable (fun x => referenceDensityFamily g L (lam,x)*
      referenceHarmonicModeEnergyDensity g lam δ R L p k
        (fun y => sphereHarmonicCoordinate hO hD k (U y)) x) := by
  obtain ⟨n,b,c,hb,hc,hcompact,hrep,hcz⟩ :=
    exists_smooth_compact_coordinates_sphereHarmonicCoordinate hO hD k U hU K hK hzero
  exact integrable_referenceHarmonicModeEnergy hF g hg lam δ R L p k hδ hR hL hp hk
    b hb c _ hc hcompact (contDiff_sphereHarmonicCoordinate hO hD k U hU) hrep

end OAI.AnisotropicCalderon.CovariantProjectedEnergy
