import Calderon.HarmonicRaisingModel
import Calderon.CovariantProjectedEnergy

set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial
open scoped ContDiff InnerProductSpace Topology
namespace OAI.AnisotropicCalderon.HarmonicProjectedCoercivity
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity
  CovariantHarmonicEnergy CovariantProjectedEnergy HarmonicRaisingModel
  FiniteProfileNormComparison RadiusProfile ReferenceDensityBounds ConformalDepth

/-- The common geometric gain for actual harmonic projections of smooth sphere fields. -/
theorem exists_referenceHarmonicProjection_uniform_coercivity (g : MatrixField)
    (hg : IsAdmissibleMetric g) (K : Set R3) (hK : IsCompact K) :
    ∃ L cRaise : ℝ, 0 < L ∧ 0 < cRaise ∧
      ∀ ε : ℝ, 0 < ε → ∃ p : ℕ, 2 ≤ p ∧ ∃ R : ℝ, 0 < R ∧
        (∀ lam ∈ Set.Icc (0:ℝ) 1, ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ x ∈ K,
          ‖fderiv ℝ (referenceRadius δ R p L) x‖ ≤ ε ∧
          referenceRadius δ R p L x * referenceProfileNorm g lam δ R p L x^2 ≤ ε) ∧
        ∀ (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
          (hD : DenseSphereHarmonics),
          ∀ lam ∈ Set.Icc (0:ℝ) 1, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
          ∀ m : ℕ, ∀ U : R3 → SphereL2, ContDiff ℝ ∞ U →
          (∀ x ∉ K, U x = 0) →
          cRaise * referenceHarmonicModeEnergy g lam δ R L p (m+1)
            (fun x => sphereHarmonicCoordinate hO hD (m+1) (U x)) ≤
            referenceHarmonicRaisingEnergy hF g L lam m
              (fun x => sphereHarmonicCoordinate hO hD (m+1) (U x))
              (referenceLogRadius δ R p L) -
            referenceHarmonicLoweringEnergy hF g L lam m
              (fun x => sphereHarmonicCoordinate hO hD (m+1) (U x))
              (referenceLogRadius δ R p L) := by
  obtain ⟨L,cRaise,hL,hcRaise,hgain⟩ :=
    exists_referenceProfileModeEnergy_uniform_coercivity.{0} g hg K hK
  refine ⟨L,cRaise,hL,hcRaise,?_⟩
  intro ε hε
  obtain ⟨p,hp,R,hR,hprofile,hfinite⟩ := hgain ε hε
  refine ⟨p,hp,R,hR,hprofile,?_⟩
  intro hF hO hD lam hlam δ hδ hδ1 m U hU hzero
  obtain ⟨n,b,c,hb,hc,hcompact,hrep,hpolyZero⟩ :=
    exists_smooth_compact_polynomial_sphereHarmonicCoordinate hF hO hD (m+1)
      U hU K hK hzero
  have hproj := contDiff_sphereHarmonicCoordinate hO hD (m+1) U hU
  have hineq := hfinite (Fin n) hF lam hlam δ hδ hδ1 m b hb c hc hcompact hpolyZero
  rw [← referenceHarmonicModeEnergy_eq_polynomial g hg lam δ R L p (m+1)
      b hb c _ hc hproj hrep,
    ← referenceHarmonicRaisingEnergy_eq_polynomial hF g hg L lam m
      b hb c _ hc hproj hrep,
    ← referenceHarmonicLoweringEnergy_eq_polynomial hF g hg L lam m
      b hb c _ hc hproj hrep] at hineq
  exact hineq

theorem integrable_referenceHarmonicProjection_energies
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (lam δ R L : ℝ) (p m : ℕ) (hδ : 0 < δ) (hR : 0 < R)
    (hL : 0 < L) (hp : 1 ≤ p)
    (U : R3 → SphereL2) (hU : ContDiff ℝ ∞ U)
    (K : Set R3) (hK : IsCompact K) (hzero : ∀ x ∉ K, U x = 0) :
    Integrable (fun x => referenceDensityFamily g L (lam,x) *
      referenceHarmonicModeEnergyDensity g lam δ R L p (m+1)
        (fun y => sphereHarmonicCoordinate hO hD (m+1) (U y)) x) ∧
    Integrable (fun x => referenceDensityFamily g L (lam,x) *
      ‖referenceHarmonicRaising hF g L lam m
        (fun y => sphereHarmonicCoordinate hO hD (m+1) (U y))
        (referenceLogRadius δ R p L) x‖^2) ∧
    Integrable (fun x => referenceDensityFamily g L (lam,x) *
      ‖referenceHarmonicLowering hF g L lam m
        (fun y => sphereHarmonicCoordinate hO hD (m+1) (U y))
        (referenceLogRadius δ R p L) x‖^2) := by
  obtain ⟨n,b,c,hb,hc,hcompact,hrep,hcz⟩ :=
    exists_smooth_compact_coordinates_sphereHarmonicCoordinate hO hD (m+1)
      U hU K hK hzero
  have hproj := contDiff_sphereHarmonicCoordinate hO hD (m+1) U hU
  have hf := contDiff_log_referenceRadius δ R p L hδ hR
  exact ⟨integrable_referenceHarmonicModeEnergy hF g hg lam δ R L p (m+1)
      hδ hR hL hp (by omega) b hb c _ hc hcompact hproj hrep,
    integrable_referenceHarmonicRaising hF g hg L lam m
      b hb c _ hc hcompact hproj hrep _ hf,
    integrable_referenceHarmonicLowering hF g hg L lam m
      b hb c _ hc hcompact hproj hrep _ hf⟩

end OAI.AnisotropicCalderon.HarmonicProjectedCoercivity
