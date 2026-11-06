import Calderon.ActualPrincipalSecondIntegration
import Calderon.WeightedRaisingBounds

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.AmbientPrincipalSecondIntegration
open SphereHarmonic SpectralCoreRegularity SpectralWeightedGraph BaseDensityAdjoint
  ReferenceDensityBounds PrincipalCommutator ActualPrincipalSecondIntegration
  LocalizedPrincipalSecondForm SectionFiveErrorForms SmoothSphereFields SmoothAngularApplication
  AmbientAngularShift WeightedRaisingBounds PerturbedDensityAdjoint ConformalDepth

lemma tsupport_ambientSphereL2_subset (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val) = 0) :
    tsupport (ambientSphereL2 G hG) ⊆ K := by
  apply closure_minimal _ hK.isClosed
  intro x hx
  by_contra hnot
  change ambientSphereL2 G hG x ≠ 0 at hx
  exact hx (ambientSphereL2_eq_zero G hG x (hz x hnot))

/-- Literal four source terms in base coordinate derivatives, on the actual ambient field. -/
def ambientPrincipalSourceNormSquare (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (g : MatrixField) (L lam δ R : ℝ) (p : ℕ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) : ℝ :=
  sourceNormSquare g L lam (referenceProfileNorm g lam δ R p L)
    (fun x k => directionalDeriv (coordinateDirection k) (ambientSphereL2 G hG) x)
    (ambientBesselField hO hD 1 (by norm_num) G hG)
    (fun x k => directionalDeriv (coordinateDirection k)
      (ambientBesselField hO hD (1/2) (by norm_num) G hG) x)
    (ambientBesselField hO hD (3/2) (by norm_num) G hG)

/-- The raw actual p A_l second-base contribution on a constructed ambient core. -/
def ambientPrincipalSecondForm (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (g : MatrixField) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (i j : Fin 3) : ℝ :=
  actualPrincipalSecondForm g L lam δ R p h (ambientSphereL2 G hG)
    (fun l => ambientDerivativeField hF hO hD l G hG) i j

/-- Integrability is constructed from actual continuous beta/inverse beta and compact fields.
No normalized beta derivative or desired energy estimate is assumed. -/
lemma integrable_ambient_principal_source_density
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (hL : 0 < L) (hδ : 0 < δ) (hR : 0 < R) (hp : 1 ≤ p)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val) = 0) :
    Integrable (fun x => referenceDensityFamily g L (lam,x) * sourceNormSquareIntegrand
      (referenceProfileNorm g lam δ R p L x)
      (fun k : Fin 3 => directionalDeriv (coordinateDirection k) (ambientSphereL2 G hG) x)
      (ambientBesselField hO hD 1 (by norm_num) G hG x)
      (fun k : Fin 3 => directionalDeriv (coordinateDirection k)
        (ambientBesselField hO hD (1/2) (by norm_num) G hG) x)
      (ambientBesselField hO hD (3/2) (by norm_num) G hG x)) := by
  let phi := ambientSphereL2 G hG
  let phiHalf := ambientBesselField hO hD (1/2 : ℝ) (by norm_num) G hG
  let phiOne := ambientBesselField hO hD 1 (by norm_num) G hG
  let phiThree := ambientBesselField hO hD (3/2 : ℝ) (by norm_num) G hG
  let beta := referenceProfileNorm g lam δ R p L
  let NN : R3 → ℝ := fun x => sourceNormSquareIntegrand (beta x)
    (fun k : Fin 3 => directionalDeriv (coordinateDirection k) phi x) (phiOne x)
    (fun k : Fin 3 => directionalDeriv (coordinateDirection k) phiHalf x) (phiThree x)
  have hphi : ContDiff ℝ ∞ phi := contDiff_ambientSphereL2 G hG
  have hhalf : ContDiff ℝ ∞ phiHalf := contDiff_ambientBesselField hO hD (1/2) (by norm_num) G hG
  have hone : ContDiff ℝ ∞ phiOne := contDiff_ambientBesselField hO hD 1 (by norm_num) G hG
  have hthree : ContDiff ℝ ∞ phiThree := contDiff_ambientBesselField hO hD (3/2) (by norm_num) G hG
  have hb : Continuous beta := continuous_referenceProfileNorm g hg lam δ R L p hδ hR
  have hbi : Continuous (fun x => (beta x)⁻¹) :=
    continuous_referenceProfileNorm_inv g hg lam δ R L p hδ hR hL hp
  have hNN : Continuous NN :=
    ((((continuous_finsetSum Finset.univ (fun k _ =>
      (contDiff_directionalDeriv (coordinateDirection k) phi hphi).continuous.norm.pow 2)).add
      ((hb.pow 2).mul (hone.continuous.norm.pow 2))).add
      (hbi.mul (continuous_finsetSum Finset.univ (fun k _ =>
        (contDiff_directionalDeriv (coordinateDirection k) phiHalf hhalf).continuous.norm.pow 2)))).add
      (hb.mul (hthree.continuous.norm.pow 2)))
  have hsupport : tsupport phi ⊆ K := tsupport_ambientSphereL2_subset G hG K hK hz
  have hsupportHalf : tsupport phiHalf ⊆ K :=
    tsupport_ambientBesselField_subset hO hD (1/2) (by norm_num) G hG K hK hz
  have hzero (x : R3) (hx : x ∉ K) : NN x = 0 := by
    have hnot : x ∉ tsupport phi := fun ht => hx (hsupport ht)
    have hnotHalf : x ∉ tsupport phiHalf := fun ht => hx (hsupportHalf ht)
    have hd (k : Fin 3) : directionalDeriv (coordinateDirection k) phi x = 0 :=
      directionalDeriv_eq_zero_of_notMem_tsupport _ phi x hnot
    have hdh (k : Fin 3) : directionalDeriv (coordinateDirection k) phiHalf x = 0 :=
      directionalDeriv_eq_zero_of_notMem_tsupport _ phiHalf x hnotHalf
    have h1 : phiOne x = 0 := ambientBesselField_eq_zero hO hD 1 (by norm_num) G hG K hz x hx
    have h3 : phiThree x = 0 := ambientBesselField_eq_zero hO hD (3/2) (by norm_num) G hG K hz x hx
    simp [NN,sourceNormSquareIntegrand,hd,hdh,h1,h3]
  have hmu : Continuous (fun x : R3 => referenceDensityFamily g L (lam,x)) :=
    ((contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id)).continuous
  have hc : HasCompactSupport (fun x => referenceDensityFamily g L (lam,x)*NN x) :=
    HasCompactSupport.intro hK (fun x hx => by rw [hzero x hx,mul_zero])
  exact (hmu.mul hNN).integrable_of_hasCompactSupport hc

/-- Fully constructed actual principal form estimate. Constants precede all shrinkage,
coefficients, fields, and ordered slots. The conclusion retains factor two and all nine slots. -/
theorem exists_ambient_principal_second_form_bound (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧
      ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∀ R : ℝ, 0 < R → ∀ p : ℕ, 1 ≤ p → ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 →
      ∀ h : MatrixField, (∀ i j, ContDiff ℝ ∞ (fun y => h y i j)) →
      (∀ x ∈ K, ∀ i j k l, TwoJetBound (coordinateDirection k) (coordinateDirection l)
        (fun y => h y i j) x (eps * referenceRadius δ R p L x)) →
      (∀ x ∈ K, 1 ≤ referenceProfileNorm g lam δ R p L x) →
      (∀ x ∈ K, referenceRadius δ R p L x * (referenceProfileNorm g lam δ R p L x)^2 ≤ eps) →
      ∀ G : R3 × R3 → ℝ, ∀ hG : ContDiff ℝ ∞ G,
      (∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val) = 0) →
      (∀ i j, |ambientPrincipalSecondForm hF hO hD g L lam δ R p h G hG i j| ≤
        C*eps * ambientPrincipalSourceNormSquare hO hD g L lam δ R p G hG) ∧
      |2 * ∑ i : Fin 3, ∑ j : Fin 3, ambientPrincipalSecondForm hF hO hD g L lam δ R p h G hG i j| ≤
        (18*C)*eps * ambientPrincipalSourceNormSquare hO hD g L lam δ R p G hG := by
  obtain ⟨C,hC,hcore⟩ := exists_actual_principal_second_core_form_bound hF hO hD g hg L hL K hK
  refine ⟨C,hC,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 h hh hhjet hb hsmall G hG hz
  have hN := integrable_ambient_principal_source_density hO hD g hg L lam δ R p hL hδ hR hp G hG K hK hz
  have hs := hcore lam hlam δ hδ hδ1 R hR p hp eps heps heps1 h hh hhjet hb hsmall
    (ambientSphereL2 G hG)
    (ambientBesselField hO hD (1/2) (by norm_num) G hG)
    (ambientBesselField hO hD 1 (by norm_num) G hG)
    (ambientBesselField hO hD (3/2) (by norm_num) G hG)
    (fun l => ambientDerivativeField hF hO hD l G hG)
    (fun l => ambientRaisingField hF hO hD l G hG)
    (contDiff_ambientSphereL2 G hG)
    (contDiff_ambientBesselField hO hD (1/2) (by norm_num) G hG)
    (fun l => contDiff_ambientDerivativeField hF hO hD l G hG)
    (fun l => contDiff_ambientRaisingField hF hO hD l G hG)
    (hasCompactSupport_ambientSphereL2 G hG K hK hz) (tsupport_ambientSphereL2_subset G hG K hK hz)
    (ambientBesselField_graph hO hD (1/2) (by norm_num) G hG)
    (ambientBesselField_graph hO hD 1 (by norm_num) G hG)
    (ambientBesselField_graph hO hD (3/2) (by norm_num) G hG)
    (fun l => ambientDerivativeField_graph hF hO hD l G hG)
    (fun l => ambientRaisingField_graph hF hO hD l G hG) hN
  have hslots (i j : Fin 3) :
      |ambientPrincipalSecondForm hF hO hD g L lam δ R p h G hG i j| ≤
        C*eps * ambientPrincipalSourceNormSquare hO hD g L lam δ R p G hG := hs i j
  refine ⟨hslots,?_⟩
  have ht := factor_two_nine_sum_bound
    (ambientPrincipalSecondForm hF hO hD g L lam δ R p h G hG)
    (C*eps * ambientPrincipalSourceNormSquare hO hD g L lam δ R p G hG) hslots
  convert ht using 1 <;> ring

end OAI.AnisotropicCalderon.AmbientPrincipalSecondIntegration
