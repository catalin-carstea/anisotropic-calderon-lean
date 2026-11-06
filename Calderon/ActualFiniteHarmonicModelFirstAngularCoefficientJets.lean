import Calderon.ActualFiniteHarmonicModelFirstAngularCoefficients
import Calderon.ActualReferenceDDHigherLogFrameJets
import Calderon.ActualMixedDensityHigherCoefficientJets
import Calderon.ActualNormalizedPrincipalDensityCoefficientJets
import Calderon.ActualReferenceDDHigherCLMProducts
import Calderon.ActualHorizontalGeometry

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open ActualReferenceDDHigherGeometryJets ActualReferenceDDHigherHCoframeJets ActualReferenceDDHigherCLMProducts
  ActualReferenceDDHigherLogFrameJets ActualMixedDensityHigherCoefficientJets ActualNormalizedPrincipalDensityCoefficientJets
  ActualPhysicalMixedReferenceCancellation ActualPhysicalMixedFirst NormalizedPrincipalMetric NormalizedPrincipalMetricSmooth
  ActualHorizontalNormBridge CoordinateBootstrapJets ConformalDepth ReferenceWeightedApproximation
  SmoothMetricFrame MovingFrameConnection AmbientReferenceRaising PrincipalCommutator ReferenceDensityBounds
theorem exists_native_first_angular_coefficients_uniform_coordinate_word_bounds
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L : ℝ) (hL : 0 < L) (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ R : ℝ, 0 < R → ∀ p : ℕ, 1 ≤ p →
      ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 → ∀ x ∈ K,
      let beta := actualReferenceBeta g1 L lam δ R p x
      1 ≤ beta →
      coordinateH8 (referenceNormalizedPrincipalDifference g1 g2 L lam) x ≤
        eps * referenceRadius δ R p L x →
      referenceRadius δ R p L x * beta^2 ≤ eps →
      ∀ w : List (Fin 3), w.length ≤ 2 → ∀ j a b c : Fin 3,
      |coordinateFieldWordPartial w
        (physicalMixedFirstCoefficient g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a j) x| ≤
        C * eps * referenceRadius δ R p L x * beta^w.length ∧
      |coordinateFieldWordPartial w (fun y =>
        physicalMixedFirstCoefficient g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a j y +
          2*referenceMetricGramFrame g1 L (lam,y) a j) x| ≤ C * beta^w.length ∧
      |coordinateFieldWordPartial w (nativeFirstDegreeCoefficient g1 g2 L lam δ R p j) x| ≤
        C * referenceRadius δ R p L x * beta^(1+w.length) ∧
      |coordinateFieldWordPartial w (nativeFirstConnectionCoefficient g1 g2 L lam δ R p j c) x| ≤
        C * referenceRadius δ R p L x * beta^w.length ∧
      |coordinateFieldWordPartial w (fun y => referenceFrameConnectionCoefficient g1 L lam y
          (referenceMetricGramFrame g1 L (lam,y) c) b a) x| ≤ C * beta^w.length ∧
      |coordinateFieldWordPartial w (fun y => referenceMetricGramFrame g1 L (lam,y) a j) x| ≤ C * beta^w.length := by
  obtain ⟨MF,hMF,hbackground⟩ := exists_mixed_background_coordinate_jet_bound g1 hg1 L K hK 2
  obtain ⟨MG,hMG,hframeGamma⟩ := exists_parameter_coordinate_word_uniform_bound
    (fun t : Fin 3 × Fin 3 × Fin 3 => fun z : ℝ × R3 => referenceFrameConnectionJoint g1 L
      (fun v : ℝ × R3 => referenceMetricGramFrame g1 L v t.1) z t.2.1 t.2.2)
    (fun t => contDiff_referenceFrameConnectionJoint g1 hg1 L
      (fun v : ℝ × R3 => referenceMetricGramFrame g1 L v t.1)
      (contDiff_referenceMetricGramFrame g1 hg1 L t.1) t.2.1 t.2.2) K hK 2
  obtain ⟨CQ,hCQ,hQwords⟩ := exists_physicalMixedFrameCoefficient_uniform_coordinate_word_bounds
    g1 hg1 L K hK 2 (by norm_num)
  obtain ⟨Cr,hCr,hRadius⟩ := exists_actual_radius_coordinate_jet_bound g1 hg1 L hL K hK 2
  obtain ⟨J,hJ,hProfile⟩ := exists_referenceDD_logRadius_frame_uniform_coordinate_word_bounds g1 hg1 L hL K hK 2
  let M : ℝ := MF+MG
  let Qc : ℝ := 1+CQ
  let Cd : ℝ := 1152*Cr*Qc*J*M
  let Ck : ℝ := 96*Cr*Qc*M
  let C : ℝ := 1+26*M+Cd+Ck
  have hMF0 : 0 ≤ MF := le_trans zero_le_one hMF
  have hMG0 : 0 ≤ MG := le_trans zero_le_one hMG
  have hM0 : 0 ≤ M := by dsimp only [M]; positivity
  have hMFM : MF ≤ M := by dsimp only [M]; linarith
  have hMGM : MG ≤ M := by dsimp only [M]; linarith
  have hQc : 0 < Qc := by dsimp only [Qc]; positivity
  have hCd : 0 ≤ Cd := by dsimp only [Cd]; positivity
  have hCk : 0 ≤ Ck := by dsimp only [Ck]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  have hCM : M ≤ C := by dsimp only [C]; linarith
  have hC24 : 24*M ≤ C := by dsimp only [C]; linarith
  have hC26 : 26*M ≤ C := by dsimp only [C]; linarith
  have hCdC : Cd ≤ C := by dsimp only [C]; linarith
  have hCkC : Ck ≤ C := by dsimp only [C]; linarith
  refine ⟨C,hC,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx beta hb hH8 hsmall w hw j a b c
  let r := referenceRadius δ R p L x
  let h := referenceNormalizedPrincipalDifference g1 g2 L lam
  let Q (u v : Fin 3) := physicalMixedQFrameCoefficient g1 L lam h u v
  let E (u t : Fin 3) (y : R3) := referenceMetricGramFrame g1 L (lam,y) u t
  let Alpha (u : Fin 3) := referenceFrameDerivative g1 L lam u (fun y => Real.log (referenceRadius δ R p L y))
  let rr := referenceRadius δ R p L
  have hr : 0 < r := referenceRadius_pos δ R p L x hδ hR
  have hb0 : 0 ≤ beta := le_trans zero_le_one hb
  have hr1 : r ≤ 1 := ((le_mul_of_one_le_right hr.le (one_le_pow₀ hb)).trans hsmall).trans heps1
  have her1 : eps*r ≤ 1 := by nlinarith
  have hpw : 1 ≤ beta^w.length := one_le_pow₀ hb
  have hpw0 : 0 ≤ beta^w.length := pow_nonneg hb0 _
  have hhS (u v : Fin 3) : ContDiff ℝ ∞ (fun y => h y u v) :=
    contDiff_referenceNormalizedPrincipalDifference_entry g1 g2 hg1 hg2 L lam u v
  have hQS (u v : Fin 3) : ContDiff ℝ ∞ (Q u v) :=
    contDiff_physicalMixedQFrameCoefficient g1 hg1 L lam h hhS u v
  have hES (u t : Fin 3) : ContDiff ℝ ∞ (E u t) :=
    (contDiff_piLp_apply (p := 2) (i := t) : ContDiff ℝ ∞ (fun z : R3 => z t)).comp
      (contDiff_referenceMetricGramFrame_slice g1 hg1 L lam u)
  have hAS (u : Fin 3) : ContDiff ℝ ∞ (Alpha u) :=
    contDiff_referenceFrameDerivative g1 hg1 L lam u _
      (contDiff_log_referenceRadius_profile δ R L p hδ hR)
  have hrS : ContDiff ℝ ∞ rr := ActualScalarPrincipalAdjoint.contDiff_referenceRadius_actual δ R p L hδ hR
  have hEwords (u t : Fin 3) : HasCoordinateWordJetBound 2 (E u t) x M beta 0 := by
    intro v hv
    have ht : |coordinateFieldWordPartial v (E u t) x| ≤ MF := (hbackground lam hlam x hx).1 v hv u t
    have hs := ht.trans hMFM
    simpa only [Real.norm_eq_abs,Nat.zero_add] using hs.trans
      (le_mul_of_one_le_right hM0 (one_le_pow₀ hb))
  have hAwords (u : Fin 3) : HasCoordinateWordJetBound 2 (Alpha u) x J beta 1 := by
    intro v hv
    simpa only [Real.norm_eq_abs,Alpha,beta,actualReferenceBeta] using
      (hProfile lam hlam δ hδ hδ1 R hR p hp x hx hb v hv).1 u
  have hrWords : HasCoordinateWordJetBound 2 rr x (Cr*r) beta 0 := by
    intro v hv
    simpa only [Real.norm_eq_abs,Nat.zero_add,mul_assoc,rr,r] using
      hRadius lam hlam δ hδ hδ1 R hR p hp x hx v hv
  have hQWords (u v : Fin 3) : HasCoordinateWordJetBound 2 (Q u v) x Qc beta 0 := by
    intro z hz
    simpa only [Real.norm_eq_abs,Nat.zero_add,Q,Qc] using
      (hQwords lam hlam δ R hδ hR p eps beta heps heps1 hb h hhS x hx hH8 hsmall u v z hz).2
  let eta (u v t : Fin 3) (y : R3) := Alpha v y*E u t y+Alpha u y*E v t y
  have hEtaS (u v t : Fin 3) : ContDiff ℝ ∞ (eta u v t) := ((hAS v).mul (hES u t)).add ((hAS u).mul (hES v t))
  have hEtaWords (u v t : Fin 3) : HasCoordinateWordJetBound 2 (eta u v t) x (8*J*M) beta 1 := by
    have hv := hasCoordinateWordJetBound_mul 2 (Alpha v) (E u t) (hAS v) (hES u t)
      x J M beta 1 0 hJ.le hM0 hb0 (hAwords v) (hEwords u t)
    have hu := hasCoordinateWordJetBound_mul 2 (Alpha u) (E v t) (hAS u) (hES v t)
      x J M beta 1 0 hJ.le hM0 hb0 (hAwords u) (hEwords v t)
    have ht := hasCoordinateWordJetBound_add 2 (fun y => Alpha v y*E u t y)
      (fun y => Alpha u y*E v t y) ((hAS v).mul (hES u t)) ((hAS u).mul (hES v t))
      x ((2:ℝ)^2*J*M) ((2:ℝ)^2*J*M) beta 1 hv hu
    have he : (2:ℝ)^2*J*M+(2:ℝ)^2*J*M=8*J*M := by ring
    rw [he] at ht
    exact ht
  have hQEWords (u v t : Fin 3) : HasCoordinateWordJetBound 2
      (fun y => Q u v y*eta u v t y) x (32*Qc*J*M) beta 1 := by
    have ht := hasCoordinateWordJetBound_mul 2 (Q u v) (eta u v t) (hQS u v) (hEtaS u v t)
      x Qc (8*J*M) beta 0 1 hQc.le (by positivity) hb0 (hQWords u v) (hEtaWords u v t)
    have he : (2:ℝ)^2*Qc*(8*J*M)=32*Qc*J*M := by ring
    rw [he] at ht
    exact ht
  have hDegreeWords (t : Fin 3) : HasCoordinateWordJetBound 2
      (nativeFirstDegreeCoefficient g1 g2 L lam δ R p t) x (Cd*r) beta 1 := by
    have hinnerS (u : Fin 3) : ContDiff ℝ ∞ (fun y => ∑ v : Fin 3, Q u v y*eta u v t y) :=
      ContDiff.sum (fun v _ => (hQS u v).mul (hEtaS u v t))
    have hinner (u : Fin 3) : HasCoordinateWordJetBound 2
        (fun y => ∑ v : Fin 3, Q u v y*eta u v t y) x (3*(32*Qc*J*M)) beta 1 := by
      simpa only [Fintype.card_fin,Nat.cast_ofNat] using hasCoordinateWordJetBound_sum 2
        (fun v : Fin 3 => fun y => Q u v y*eta u v t y) (fun v => (hQS u v).mul (hEtaS u v t))
        x (32*Qc*J*M) beta 1 (fun v => hQEWords u v t)
    have hs := hasCoordinateWordJetBound_sum 2
      (fun u : Fin 3 => fun y => ∑ v : Fin 3, Q u v y*eta u v t y) hinnerS
      x (3*(32*Qc*J*M)) beta 1 hinner
    have hs' : HasCoordinateWordJetBound 2
        (fun y => ∑ u : Fin 3, ∑ v : Fin 3, Q u v y*eta u v t y) x (288*Qc*J*M) beta 1 := by
      have he : (3:ℝ)*(3*(32*Qc*J*M))=288*Qc*J*M := by ring
      simpa only [Fintype.card_fin,Nat.cast_ofNat,he] using hs
    have ht := hasCoordinateWordJetBound_mul 2 rr
      (fun y => ∑ u : Fin 3, ∑ v : Fin 3, Q u v y*eta u v t y) hrS
      (ContDiff.sum (fun u _ => hinnerS u)) x (Cr*r) (288*Qc*J*M) beta 0 1
      (mul_nonneg hCr.le hr.le) (by positivity) hb0 hrWords hs'
    have he : (2:ℝ)^2*(Cr*r)*(288*Qc*J*M)=Cd*r := by dsimp only [Cd]; ring
    rw [he] at ht
    exact ht
  have hQeWords (u v t : Fin 3) : HasCoordinateWordJetBound 2
      (fun y => Q u v y*E u t y) x (4*Qc*M) beta 0 := by
    have ht := hasCoordinateWordJetBound_mul 2 (Q u v) (E u t) (hQS u v) (hES u t)
      x Qc M beta 0 0 hQc.le hM0 hb0 (hQWords u v) (hEwords u t)
    simpa only [show (2:ℝ)^2=4 by norm_num,Nat.zero_add] using ht
  have heQWords (u v t : Fin 3) : HasCoordinateWordJetBound 2
      (fun y => Q u v y*E v t y) x (4*Qc*M) beta 0 := by
    have ht := hasCoordinateWordJetBound_mul 2 (Q u v) (E v t) (hQS u v) (hES v t)
      x Qc M beta 0 0 hQc.le hM0 hb0 (hQWords u v) (hEwords v t)
    simpa only [show (2:ℝ)^2=4 by norm_num,Nat.zero_add] using ht
  have hConnectionWords (t v : Fin 3) : HasCoordinateWordJetBound 2
      (nativeFirstConnectionCoefficient g1 g2 L lam δ R p t v) x (Ck*r) beta 0 := by
    have hleftS : ContDiff ℝ ∞ (fun y => ∑ u : Fin 3, Q u v y*E u t y) :=
      ContDiff.sum (fun u _ => (hQS u v).mul (hES u t))
    have hrightS : ContDiff ℝ ∞ (fun y => ∑ u : Fin 3, Q v u y*E u t y) :=
      ContDiff.sum (fun u _ => (hQS v u).mul (hES u t))
    have hl : HasCoordinateWordJetBound 2 (fun y => ∑ u : Fin 3, Q u v y*E u t y)
        x (12*Qc*M) beta 0 := by
      simpa only [Fintype.card_fin,Nat.cast_ofNat,show (3:ℝ)*(4*Qc*M)=12*Qc*M by ring] using
        hasCoordinateWordJetBound_sum 2 (fun u : Fin 3 => fun y => Q u v y*E u t y)
          (fun u => (hQS u v).mul (hES u t)) x (4*Qc*M) beta 0 (fun u => hQeWords u v t)
    have hrw : HasCoordinateWordJetBound 2 (fun y => ∑ u : Fin 3, Q v u y*E u t y)
        x (12*Qc*M) beta 0 := by
      simpa only [Fintype.card_fin,Nat.cast_ofNat,show (3:ℝ)*(4*Qc*M)=12*Qc*M by ring] using
        hasCoordinateWordJetBound_sum 2 (fun u : Fin 3 => fun y => Q v u y*E u t y)
          (fun u => (hQS v u).mul (hES u t)) x (4*Qc*M) beta 0 (fun u => heQWords v u t)
    have hs := hasCoordinateWordJetBound_add 2 (fun y => ∑ u : Fin 3, Q u v y*E u t y)
      (fun y => ∑ u : Fin 3, Q v u y*E u t y) hleftS hrightS x (12*Qc*M) (12*Qc*M) beta 0 hl hrw
    have hs' : HasCoordinateWordJetBound 2
        (fun y => (∑ u : Fin 3, Q u v y*E u t y)+(∑ u : Fin 3, Q v u y*E u t y)) x (24*Qc*M) beta 0 := by
      simpa only [show 12*Qc*M+12*Qc*M=24*Qc*M by ring] using hs
    have ht := hasCoordinateWordJetBound_mul 2 rr
      (fun y => (∑ u : Fin 3, Q u v y*E u t y)+(∑ u : Fin 3, Q v u y*E u t y)) hrS
      (hleftS.add hrightS) x (Cr*r) (24*Qc*M) beta 0 0 (mul_nonneg hCr.le hr.le)
      (by positivity) hb0 hrWords hs'
    have he : (2:ℝ)^2*(Cr*r)*(24*Qc*M)=Ck*r := by dsimp only [Ck]; ring
    rw [he] at ht
    exact ht
  have hMixed : |coordinateFieldWordPartial w (physicalMixedFirstCoefficient g1 L lam h a j) x| ≤ 24*M*eps*r := by
    have ht := abs_physicalMixedFirstCoefficient_coordinate_word_le g1 g2 hg1 hg2 L lam x
      eps r MF 2 (by norm_num) heps hr.le hMF0 (hbackground lam hlam x hx) hH8 w hw a j
    have hs : 6*(2:ℝ)^2*MF*eps*r ≤ 24*M*eps*r := by
      norm_num only [show (2:ℝ)^2=4 by norm_num]
      nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hMFM heps) hr.le]
    exact ht.trans hs
  have hMixedBeta : |coordinateFieldWordPartial w (physicalMixedFirstCoefficient g1 L lam h a j) x| ≤ 24*M*eps*r*beta^w.length :=
    hMixed.trans (le_mul_of_one_le_right (by positivity) hpw)
  have hFrame : |coordinateFieldWordPartial w (E a j) x| ≤ M*beta^w.length := by
    simpa only [Real.norm_eq_abs,Nat.zero_add] using hEwords a j w hw
  have hFull : |coordinateFieldWordPartial w
      (fun y => physicalMixedFirstCoefficient g1 L lam h a j y+2*E a j y) x| ≤ 26*M*beta^w.length := by
    have hmS := contDiff_physicalMixedFirstCoefficient g1 hg1 L lam h hhS a j
    rw [ActualMixedDensityHigherCoefficientJets.coordinateFieldWordPartial_add w _ _ hmS (contDiff_const.mul (hES a j)),
      coordinateFieldWordPartial_const_mul w 2 _ (hES a j)]
    calc
      _ ≤ |coordinateFieldWordPartial w (physicalMixedFirstCoefficient g1 L lam h a j) x|+
          |2*coordinateFieldWordPartial w (E a j) x| := abs_add_le _ _
      _ ≤ 24*M*eps*r*beta^w.length+2*(M*beta^w.length) := add_le_add hMixedBeta (by
        rw [abs_mul]
        simpa only [show |(2:ℝ)|=2 by norm_num] using mul_le_mul_of_nonneg_left hFrame (by norm_num : (0:ℝ)≤2))
      _ ≤ 26*M*beta^w.length := by nlinarith [mul_le_mul_of_nonneg_left her1 (mul_nonneg hM0 hpw0)]
  have hGamma : |coordinateFieldWordPartial w (fun y => referenceFrameConnectionCoefficient g1 L lam y
      (referenceMetricGramFrame g1 L (lam,y) c) b a) x| ≤ M*beta^w.length := by
    have ht := hframeGamma lam hlam x hx (c,b,a) w hw
    have hs : |coordinateFieldWordPartial w (fun y => referenceFrameConnectionCoefficient g1 L lam y
        (referenceMetricGramFrame g1 L (lam,y) c) b a) x| ≤ MG := by
      simpa only [referenceFrameConnectionJoint_eq g1 hg1 L,Real.norm_eq_abs] using ht
    exact (hs.trans hMGM).trans (le_mul_of_one_le_right hM0 hpw)
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · exact hMixedBeta.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC24 heps) hr.le) hpw0)
  · exact hFull.trans (mul_le_mul_of_nonneg_right hC26 hpw0)
  · have ht : |coordinateFieldWordPartial w (nativeFirstDegreeCoefficient g1 g2 L lam δ R p j) x| ≤
        Cd*r*beta^(1+w.length) := by simpa only [Real.norm_eq_abs] using hDegreeWords j w hw
    exact ht.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCdC hr.le) (pow_nonneg hb0 _))
  · have ht : |coordinateFieldWordPartial w (nativeFirstConnectionCoefficient g1 g2 L lam δ R p j c) x| ≤
        Ck*r*beta^w.length := by simpa only [Real.norm_eq_abs,Nat.zero_add] using hConnectionWords j c w hw
    exact ht.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCkC hr.le) hpw0)
  · exact hGamma.trans (mul_le_mul_of_nonneg_right hCM hpw0)
  · exact hFrame.trans (mul_le_mul_of_nonneg_right hCM hpw0)

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
