import Calderon.ActualFiniteHarmonicModelScalarOperatorHalfForms
import Calderon.ActualFiniteHarmonicModelPrincipalHWordsBounds
import Calderon.ActualFiniteHarmonicModelFirstBalancedAngularBounds

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore ActualModelCommutatorWords SpectralWeightedGraph
  ReferenceDensityBounds ReferenceWeightedApproximation PrincipalCommutator
  BaseDensityAdjoint CoordinateBootstrapJets NormalizedPrincipalMetric ConformalDepth
  ActualScalarPrincipalAdjoint ActualNormalizedPrincipalDensityCoefficientJets
  ActualReferenceDDHigherGeometryJets ActualMixedDensityScalarZeroForm NormalizedPrincipalMetricSmooth
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev principalHHalfFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] principalHHalfFunction
attribute [local irreducible] nativeH

theorem exists_nativePrincipal_H_uniform_half_word_bounds
    (hF : SphereFischerInner) (g1 g2 : MatrixField)
    (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L : ℝ) (hL : 0 < L) (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, ∀ hδ : 0 < δ, δ ≤ 1 → ∀ R : ℝ, ∀ hR : 0 < R,
      ∀ p : ℕ, 1 ≤ p → ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 → ∀ x ∈ K,
      let beta := actualReferenceBeta g1 L lam δ R p x
      1 ≤ beta →
      coordinateH8 (referenceNormalizedPrincipalDifference g1 g2 L lam) x ≤
        eps * referenceRadius δ R p L x →
      referenceRadius δ R p L x * beta^2 ≤ eps →
      ∀ i k l j m : Fin 3, ∀ U V : smoothCompactFiniteSphereCore hO hD,
      let d := fun s => coreDirectionalDerivative hO hD (coordinateDirection s)
      let a := nativePrincipalCoefficient hO hD g1 g2 hg1 L lam δ R p hg2 hδ hR i k
      let H := nativeH hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR l
      let n := ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) U x‖ *
        ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) V x‖
      |⟪(H*coefficientDerivative (d j) a) U x,V x⟫_ℝ| ≤ (C*eps/beta)*n ∧
      |⟪coefficientDerivative (d m) (H*coefficientDerivative (d j) a) U x,V x⟫_ℝ| ≤ (C*eps)*n ∧
      |⟪(a*coefficientDerivative (d j) H) U x,V x⟫_ℝ| ≤ (C*eps/beta)*n ∧
      |⟪coefficientDerivative (d m) (a*coefficientDerivative (d j) H) U x,V x⟫_ℝ| ≤ (C*eps)*n ∧
      |⟪(a*coefficientDerivative (d m) (coefficientDerivative (d j) H)) U x,V x⟫_ℝ| ≤ (C*eps)*n := by
  obtain ⟨M,hM,hgeom⟩ := exists_mixed_principal_density_background_jet_bound g1 hg1 L K hK 2
  obtain ⟨Cr,hCr,hRadius⟩ := exists_actual_radius_coordinate_jet_bound g1 hg1 L hL K hK 2
  obtain ⟨CH,hCH,hH⟩ := exists_nativeH_uniform_half_angular_forms hO hD hF g1 g2 hg1 hg2 L hL K hK
  let Cp : ℝ := normalizedPrincipalCoordinateJetConstant 2*Cr*M
  have hCp : 0 < Cp := by dsimp only [Cp,normalizedPrincipalCoordinateJetConstant]; positivity
  let C : ℝ := 2*Cp*CH
  have hC : 0 < C := mul_pos (mul_pos (by norm_num) hCp) hCH
  refine ⟨C,hC,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx beta hb hH8 hsmall i k l j m U V d a H n
  let r := referenceRadius δ R p L x
  let c : R3 → ℝ := fun y => actualPrincipalMatrix g1 L lam δ R p
    (referenceNormalizedPrincipalDifference g1 g2 L lam) y i k
  have hc : ContDiff ℝ ∞ c := ActualPerturbedDefect.contDiff_actualPrincipalMatrix_entry g1 hg1 L lam δ R p
    (referenceNormalizedPrincipalDifference g1 g2 L lam) hδ hR
    (fun b s => contDiff_referenceNormalizedPrincipalDifference_entry g1 g2 hg1 hg2 L lam b s) i k
  have ha : a = coreScalar hO hD c hc := by
    apply LinearMap.ext
    intro G
    apply Subtype.ext
    funext y
    exact nativePrincipalCoefficient_apply_eq_actualPrincipal hO hD g1 g2 hg1 L lam δ R p hg2 hδ hR i k G y
  have hr : 0 < r := referenceRadius_pos δ R p L x hδ hR
  have hbpos : 0 < beta := lt_of_lt_of_le zero_lt_one hb
  have hb0 : 0 ≤ beta := hbpos.le
  change r*beta^2 ≤ eps at hsmall
  have hr1 : r ≤ 1 := ((le_mul_of_one_le_right hr.le (one_le_pow₀ hb)).trans hsmall).trans heps1
  have hsm1 : eps*referenceRadius δ R p L x ≤ 1 := by change eps*r ≤ 1; nlinarith
  have hjets (w : List (Fin 3)) (hw : w.length ≤ 2) :
      |coordinateFieldWordPartial w c x| ≤ Cp*r*beta^w.length :=
    abs_actualNormalizedPrincipal_coordinate_word_le g1 g2 hg1 hg2 L lam δ R p x eps M Cr 2 (by norm_num)
      hδ hR heps hM hCr.le hsm1 hb (hgeom lam hlam x hx)
      (hRadius lam hlam δ hδ hδ1 R hR p hp x hx) hH8 w hw i k
  have hc0 : |c x| ≤ Cp*r := by
    simpa only [coordinateFieldWordPartial,List.length_nil,pow_zero,mul_one] using hjets [] (by simp)
  have hc1 (s : Fin 3) : |directionalFDeriv (coordinateDirection s) c x| ≤ Cp*r*beta := by
    simpa only [coordinateFieldWordPartial,List.length_cons,List.length_nil,Nat.reduceAdd,pow_one] using hjets [s] (by simp)
  have hc2 : |directionalFDeriv (coordinateDirection m) (directionalFDeriv (coordinateDirection j) c) x| ≤ Cp*r*beta^2 := by
    simpa only [coordinateFieldWordPartial,List.length_cons,List.length_nil,Nat.reduceAdd] using hjets [m,j] (by simp)
  have hforms (s t : Fin 3) := hH lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx hb hH8 hsmall l s t U V
  have h0 : |⟪H U x,V x⟫_ℝ| ≤ CH*n := by simpa only [n,mul_assoc] using (hforms j m).1
  have h1 (s : Fin 3) : |⟪coefficientDerivative (d s) H U x,V x⟫_ℝ| ≤ (CH*beta)*n := by
    simpa only [n,mul_assoc] using (hforms s m).2.1
  have h2 : |⟪coefficientDerivative (d m) (coefficientDerivative (d j) H) U x,V x⟫_ℝ| ≤ (CH*beta^2)*n := by
    simpa only [n,mul_assoc] using (hforms m j).2.2
  have hn : 0 ≤ n := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hrate : r*beta ≤ eps/beta := (le_div_iff₀ hbpos).mpr (by nlinarith [hsmall])
  have hscale0 : Cp*CH*(r*beta) ≤ C*eps/beta := by
    calc
      _ ≤ Cp*CH*(eps/beta) := mul_le_mul_of_nonneg_left hrate (mul_nonneg hCp.le hCH.le)
      _ ≤ C*(eps/beta) := mul_le_mul_of_nonneg_right (by dsimp only [C]; nlinarith [mul_pos hCp hCH]) (div_nonneg heps hb0)
      _ = _ := by ring
  have hscale1 : 2*Cp*CH*(r*beta^2) ≤ C*eps := by
    exact mul_le_mul_of_nonneg_left hsmall hC.le
  have hleft : H*coefficientDerivative (d j) a =
      coreScalar hO hD (directionalFDeriv (coordinateDirection j) c)
        (contDiff_directionalFDeriv _ c hc)*H := by
    rw [ha,coefficientDerivative_coreScalar]
    exact (nativeH_scalarCentral hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR l _ _).eq
  have hB0 : |directionalFDeriv (coordinateDirection j) c x| *CH ≤ C*eps/beta := by
    calc
      _ ≤ (Cp*r*beta)*CH := mul_le_mul_of_nonneg_right (hc1 j) hCH.le
      _ = Cp*CH*(r*beta) := by ring
      _ ≤ _ := hscale0
  have hB1 : |directionalFDeriv (coordinateDirection m) (directionalFDeriv (coordinateDirection j) c) x| *CH +
      |directionalFDeriv (coordinateDirection j) c x| *(CH*beta) ≤ C*eps := by
    calc
      _ ≤ (Cp*r*beta^2)*CH+(Cp*r*beta)*(CH*beta) := add_le_add
        (mul_le_mul_of_nonneg_right hc2 hCH.le)
        (mul_le_mul_of_nonneg_right (hc1 j) (mul_nonneg hCH.le hb0))
      _ = 2*Cp*CH*(r*beta^2) := by ring
      _ ≤ _ := hscale1
  have hB2 : |c x| *(CH*beta) ≤ C*eps/beta := by
    calc
      _ ≤ (Cp*r)*(CH*beta) := mul_le_mul_of_nonneg_right hc0 (mul_nonneg hCH.le hb0)
      _ = Cp*CH*(r*beta) := by ring
      _ ≤ _ := hscale0
  have hB3 : |directionalFDeriv (coordinateDirection m) c x| *(CH*beta)+|c x| *(CH*beta^2) ≤ C*eps := by
    calc
      _ ≤ (Cp*r*beta)*(CH*beta)+(Cp*r)*(CH*beta^2) := add_le_add
        (mul_le_mul_of_nonneg_right (hc1 m) (mul_nonneg hCH.le hb0))
        (mul_le_mul_of_nonneg_right hc0 (mul_nonneg hCH.le (sq_nonneg beta)))
      _ = 2*Cp*CH*(r*beta^2) := by ring
      _ ≤ _ := hscale1
  have hB4 : |c x| *(CH*beta^2) ≤ C*eps := by
    calc
      _ ≤ (Cp*r)*(CH*beta^2) := mul_le_mul_of_nonneg_right hc0 (mul_nonneg hCH.le (sq_nonneg beta))
      _ ≤ 2*Cp*CH*(r*beta^2) := by nlinarith [mul_nonneg (mul_nonneg hCp.le hCH.le) (mul_nonneg hr.le (sq_nonneg beta))]
      _ ≤ _ := hscale1
  have hleft0 := abs_inner_coreScalar_mul_le_half_forms hO hD (directionalFDeriv (coordinateDirection j) c) (contDiff_directionalFDeriv (coordinateDirection j) c hc) H U V x CH
    (by simpa only [n,mul_assoc] using h0)
  have hleft1 := abs_inner_coefficientDerivative_coreScalar_mul_le_half_forms hO hD (coordinateDirection m)
    (directionalFDeriv (coordinateDirection j) c) (contDiff_directionalFDeriv (coordinateDirection j) c hc) H U V x CH (CH*beta)
    (by simpa only [n,mul_assoc] using h0) (by simpa only [n,mul_assoc] using h1 m)
  have hright0 := abs_inner_coreScalar_mul_le_half_forms hO hD c hc (coefficientDerivative (d j) H) U V x (CH*beta)
    (by simpa only [n,mul_assoc] using h1 j)
  have hright1 := abs_inner_coefficientDerivative_coreScalar_mul_le_half_forms hO hD (coordinateDirection m)
    c hc (coefficientDerivative (d j) H) U V x (CH*beta) (CH*beta^2)
    (by simpa only [n,mul_assoc] using h1 j) (by simpa only [n,mul_assoc] using h2)
  have hzero := abs_inner_coreScalar_mul_le_half_forms hO hD c hc
    (coefficientDerivative (d m) (coefficientDerivative (d j) H)) U V x (CH*beta^2)
    (by simpa only [n,mul_assoc] using h2)
  simp only [← mul_assoc] at hleft0 hleft1 hright0 hright1 hzero
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [hleft]
    exact hleft0.trans (by simpa only [n,mul_assoc] using mul_le_mul_of_nonneg_right hB0 hn)
  · rw [hleft]
    exact hleft1.trans (by simpa only [n,mul_assoc] using mul_le_mul_of_nonneg_right hB1 hn)
  · rw [ha]
    exact hright0.trans (by simpa only [n,mul_assoc] using mul_le_mul_of_nonneg_right hB2 hn)
  · rw [ha]
    exact hright1.trans (by simpa only [n,mul_assoc] using mul_le_mul_of_nonneg_right hB3 hn)
  · rw [ha]
    exact hzero.trans (by simpa only [n,mul_assoc] using mul_le_mul_of_nonneg_right hB4 hn)

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
