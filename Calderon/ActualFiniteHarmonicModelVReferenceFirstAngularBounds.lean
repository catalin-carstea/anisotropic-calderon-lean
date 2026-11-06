import Calderon.ActualFiniteHarmonicModelVReferenceFirstAngularJets
import Calderon.ActualFiniteHarmonicModelFirstAngularCoefficientJets

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph BoundedAngularShift BalancedAngularShift
  ActualAngularDerivativeRaisingCommutator ActualPhysicalMixedFirst NormalizedPrincipalMetric NormalizedPrincipalMetricSmooth
  ActualReferenceDDHigherGeometryJets ActualReferenceDDHigherHCoframeJets ActualReferenceDDHigherCLMProducts
  SmoothMetricFrame MovingFrameConnection AmbientReferenceCovariantCore PrincipalCommutator ReferenceDensityBounds
  CoordinateBootstrapJets ConformalDepth ReferenceWeightedApproximation
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev nativeVRFirstQuantFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] nativeVRFirstQuantFunction
theorem exists_nativeVReferenceFirstBalancedAngularCoefficient_uniform_coordinate_word_bound
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L : ℝ) (hL : 0 < L) (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, ∀ hδ : 0 < δ, δ ≤ 1 → ∀ R : ℝ, ∀ hR : 0 < R, ∀ p : ℕ, 1 ≤ p →
      ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 → ∀ x ∈ K,
      let beta := actualReferenceBeta g1 L lam δ R p x
      1 ≤ beta →
      coordinateH8 (referenceNormalizedPrincipalDifference g1 g2 L lam) x ≤
        eps * referenceRadius δ R p L x →
      referenceRadius δ R p L x * beta^2 ≤ eps →
      ∀ l i : Fin 3, ∀ w : List (Fin 3), w.length ≤ 2 →
      ‖coordinateFieldWordPartial w (nativeVReferenceFirstBalancedAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p l i) x‖ ≤
        (C * eps / beta) * beta^w.length := by
  obtain ⟨J,hJ,hCoeff⟩ := exists_native_first_angular_coefficients_uniform_coordinate_word_bounds g1 g2 hg1 hg2 L hL K hK
  let C : ℝ := 1+2352*J^2
  refine ⟨C,by dsimp only [C]; positivity,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx beta hb hH8 hsmall l i w hw
  let r := referenceRadius δ R p L x
  let rate := eps/beta
  let E (b : Fin 3) (y : R3) := referenceMetricGramFrame g1 L (lam,y) b i
  let m (a : Fin 3) := physicalMixedFirstCoefficient g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a l
  let d := nativeFirstDegreeCoefficient g1 g2 L lam δ R p l
  let Rop (b : Fin 3) := balancedRaising hF hO hD b
  let DR (a b : Fin 3) := normalizedDerivativeRaisingCommutator hF hO hD a b
  have hr : 0 < r := referenceRadius_pos δ R p L x hδ hR
  have hbpos : 0 < beta := by linarith
  have hb0 : 0 ≤ beta := hbpos.le
  have hrate : 0 ≤ rate := div_nonneg heps hb0
  change r*beta^2 ≤ eps at hsmall
  have hrb : r*beta ≤ rate := (le_div_iff₀ hbpos).2 (by nlinarith)
  have her : eps*r ≤ rate := (mul_le_of_le_one_left hr.le heps1).trans
    ((le_mul_of_one_le_right hr.le hb).trans hrb)
  have hES (b : Fin 3) : ContDiff ℝ ∞ (E b) :=
    (contDiff_piLp_apply (p := 2) (i := i) : ContDiff ℝ ∞ (fun z : R3 => z i)).comp
      (contDiff_referenceMetricGramFrame_slice g1 hg1 L lam b)
  have hmS (a : Fin 3) : ContDiff ℝ ∞ (m a) := contDiff_physicalMixedFirstCoefficient g1 hg1 L lam _
    (fun s t => contDiff_referenceNormalizedPrincipalDifference_entry g1 g2 hg1 hg2 L lam s t) a l
  have hdS := contDiff_nativeFirstDegreeCoefficient g1 g2 hg1 hg2 L lam δ R p hδ hR l
  have hc (v : List (Fin 3)) (hv : v.length ≤ 2) (j a b c : Fin 3) :=
    hCoeff lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx hb hH8 hsmall v hv j a b c
  have hEj (b : Fin 3) : HasCoordinateWordJetBound 2 (E b) x J beta 0 := by
    intro v hv
    simpa only [E,Real.norm_eq_abs,Nat.zero_add] using (hc v hv i b 0 0).2.2.2.2.2
  have hmj (a : Fin 3) : HasCoordinateWordJetBound 2 (m a) x (J*eps*r) beta 0 := by
    intro v hv
    simpa only [m,Real.norm_eq_abs,Nat.zero_add,mul_assoc] using (hc v hv l a 0 0).1
  have hdj : HasCoordinateWordJetBound 2 d x (J*r) beta 1 := by
    intro v hv
    simpa only [d,Real.norm_eq_abs,mul_assoc] using (hc v hv l 0 0 0).2.2.1
  have hFixed (z : R3 → ℝ) (hz : ContDiff ℝ ∞ z) (S : SphereL2 →L[ℝ] SphereL2)
      (B M : ℝ) (s : ℕ) (hB : 0 ≤ B) (hM : 0 ≤ M) (hS : ‖S‖ ≤ M)
      (hj : HasCoordinateWordJetBound 2 z x B beta s) :
      HasCoordinateWordJetBound 2 (fun y => z y • S) x (4*B*M) beta s := by
    have hSj := hasCoordinateWordJetBound_const_normed 2 S x M beta hS hb0
    have ht := hasCoordinateWordJetBound_smul 2 z (fun _ : R3 => S) hz contDiff_const
      x B M beta s 0 hB hM hb0 hj hSj
    simpa only [show (2:ℝ)^2=4 by norm_num,Nat.add_zero] using ht
  have h2d : HasCoordinateWordJetBound 2 (fun y => 2*d y) x (2*J*r) beta 1 := by
    intro v hv
    rw [ActualMixedDensityHigherCoefficientJets.coordinateFieldWordPartial_const_mul v 2 d hdS,Real.norm_eq_abs,abs_mul]
    simpa only [Real.norm_eq_abs,show |(2:ℝ)|=2 by norm_num,mul_assoc] using
      mul_le_mul_of_nonneg_left (hdj v hv) (by norm_num : (0:ℝ)≤2)
  have hRaiseScalar (b : Fin 3) : HasCoordinateWordJetBound 2 (fun y => E b y*(2*d y)) x (8*J^2*r) beta 1 := by
    have ht := hasCoordinateWordJetBound_mul 2 (E b) (fun y => 2*d y) (hES b) (contDiff_const.mul hdS)
      x J (2*J*r) beta 0 1 hJ.le (by positivity) hb0 (hEj b) h2d
    convert ht using 1 <;> simp only [show (2:ℝ)^2=4 by norm_num,Nat.zero_add] <;> ring
  have hDRScalar (b a : Fin 3) : HasCoordinateWordJetBound 2 (fun y => E b y*m a y) x (4*J^2*eps*r) beta 0 := by
    have ht := hasCoordinateWordJetBound_mul 2 (E b) (m a) (hES b) (hmS a)
      x J (J*eps*r) beta 0 0 hJ.le (by positivity) hb0 (hEj b) (hmj a)
    convert ht using 1 <;> simp only [show (2:ℝ)^2=4 by norm_num,Nat.zero_add] <;> ring
  let FR (y : R3) := ∑ b : Fin 3, (E b y*(2*d y)) • Rop b
  let FDR (y : R3) := ∑ b : Fin 3, ∑ a : Fin 3, (E b y*m a y) • DR a b
  have hFRS : ContDiff ℝ ∞ FR := ContDiff.sum (fun b _ => ((hES b).mul (contDiff_const.mul hdS)).smul contDiff_const)
  have hFDRS : ContDiff ℝ ∞ FDR := ContDiff.sum (fun b _ => ContDiff.sum (fun a _ => ((hES b).mul (hmS a)).smul contDiff_const))
  have hRaiseTerm (b : Fin 3) : HasCoordinateWordJetBound 2 (fun y => (E b y*(2*d y)) • Rop b) x (64*J^2*r) beta 1 := by
    have ht := hFixed _ ((hES b).mul (contDiff_const.mul hdS)) (Rop b) (8*J^2*r) 2 1
      (by positivity) (by norm_num) (norm_balancedRaising_le hF hO hD b) (hRaiseScalar b)
    convert ht using 1 <;> ring
  have hDRTerm (b a : Fin 3) : HasCoordinateWordJetBound 2 (fun y => (E b y*m a y) • DR a b) x (240*J^2*eps*r) beta 0 := by
    have ht := hFixed _ ((hES b).mul (hmS a)) (DR a b) (4*J^2*eps*r) 15 0
      (by positivity) (by norm_num) (norm_normalizedDerivativeRaisingCommutator_le hF hO hD a b) (hDRScalar b a)
    convert ht using 1 <;> ring
  have hRsum : HasCoordinateWordJetBound 2 FR x (192*J^2*r) beta 1 := by
    have ht := hasCoordinateWordJetBound_sum 2 (fun b y => (E b y*(2*d y)) • Rop b)
      (fun b => ((hES b).mul (contDiff_const.mul hdS)).smul contDiff_const) x (64*J^2*r) beta 1 hRaiseTerm
    convert ht using 1 <;> simp only [Fintype.card_fin,Nat.cast_ofNat] <;> ring
  have hDRsum : HasCoordinateWordJetBound 2 FDR x (2160*J^2*eps*r) beta 0 := by
    have hinner (b : Fin 3) := hasCoordinateWordJetBound_sum 2 (fun a y => (E b y*m a y) • DR a b)
      (fun a => ((hES b).mul (hmS a)).smul contDiff_const) x (240*J^2*eps*r) beta 0 (hDRTerm b)
    have ht := hasCoordinateWordJetBound_sum 2 (fun b y => ∑ a : Fin 3, (E b y*m a y) • DR a b)
      (fun b => ContDiff.sum (fun a _ => ((hES b).mul (hmS a)).smul contDiff_const))
      x ((Fintype.card (Fin 3):ℝ)*(240*J^2*eps*r)) beta 0 hinner
    convert ht using 1 <;> simp only [Fintype.card_fin,Nat.cast_ofNat] <;> ring
  have hRsmall : HasCoordinateWordJetBound 2 FR x (192*J^2*rate) beta 0 := by
    intro v hv
    calc
      _ ≤ (192*J^2*r)*beta^(1+v.length) := hRsum v hv
      _ = (192*J^2)*(r*beta)*beta^v.length := by rw [pow_add]; ring
      _ ≤ (192*J^2*rate)*beta^(0+v.length) := by
        simpa only [Nat.zero_add] using mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hrb (by positivity)) (pow_nonneg hb0 _)
  have hDRsmall : HasCoordinateWordJetBound 2 FDR x (2160*J^2*rate) beta 0 := by
    intro v hv
    exact (hDRsum v hv).trans (mul_le_mul_of_nonneg_right
      (by nlinarith [mul_le_mul_of_nonneg_left her (by positivity : 0 ≤ 2160*J^2)]) (pow_nonneg hb0 _))
  have hnR := hasCoordinateWordJetBound_neg 2 FR hFRS x (192*J^2*rate) beta 0 hRsmall
  have ht := hasCoordinateWordJetBound_sub 2 (fun y => -FR y) FDR hFRS.neg hFDRS
    x (192*J^2*rate) (2160*J^2*rate) beta 0 hnR hDRsmall
  change HasCoordinateWordJetBound 2 (nativeVReferenceFirstBalancedAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p l i)
    x (192*J^2*rate+2160*J^2*rate) beta 0 at ht
  calc
    _ ≤ (192*J^2*rate+2160*J^2*rate)*beta^w.length := by simpa only [Nat.zero_add] using ht w hw
    _ ≤ (C*rate)*beta^w.length := mul_le_mul_of_nonneg_right
      (by dsimp only [C]; nlinarith) (pow_nonneg hb0 _)
    _ = _ := by dsimp only [rate]; ring

theorem exists_nativeVReferenceFirst_uniform_half_angular_forms
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L : ℝ) (hL : 0 < L) (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, ∀ hδ : 0 < δ, δ ≤ 1 → ∀ R : ℝ, ∀ hR : 0 < R, ∀ p : ℕ, 1 ≤ p →
      ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 → ∀ x ∈ K,
      let beta := actualReferenceBeta g1 L lam δ R p x
      1 ≤ beta →
      coordinateH8 (referenceNormalizedPrincipalDifference g1 g2 L lam) x ≤
        eps * referenceRadius δ R p L x →
      referenceRadius δ R p L x * beta^2 ≤ eps →
      ∀ l i j k : Fin 3, ∀ F G : smoothCompactFiniteSphereCore hO hD,
      |⟪(ActualModelCommutatorWords.commutator (nativeV hO hD hF g1 g2 hg1 L lam δ R p l hg2 hδ hR) (nativeReferenceFirstCoefficient hO hD hF g1 hg1 L lam δ R p hδ hR i)) F x,G x⟫_ℝ| ≤ (C * eps / beta) * ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖ *
          ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x‖ ∧
      |⟪ActualModelCommutatorWords.coefficientDerivative (coreDirectionalDerivative hO hD (coordinateDirection j))
        (ActualModelCommutatorWords.commutator (nativeV hO hD hF g1 g2 hg1 L lam δ R p l hg2 hδ hR) (nativeReferenceFirstCoefficient hO hD hF g1 hg1 L lam δ R p hδ hR i)) F x,G x⟫_ℝ| ≤ (C * eps) * ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖ *
          ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x‖ ∧
      |⟪ActualModelCommutatorWords.coefficientDerivative (coreDirectionalDerivative hO hD (coordinateDirection j))
        (ActualModelCommutatorWords.coefficientDerivative (coreDirectionalDerivative hO hD (coordinateDirection k))
          (ActualModelCommutatorWords.commutator (nativeV hO hD hF g1 g2 hg1 L lam δ R p l hg2 hδ hR) (nativeReferenceFirstCoefficient hO hD hF g1 hg1 L lam δ R p hδ hR i))) F x,G x⟫_ℝ| ≤ (C * eps * beta) * ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖ *
          ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x‖ := by
  obtain ⟨C,hC,hJet⟩ := exists_nativeVReferenceFirstBalancedAngularCoefficient_uniform_coordinate_word_bound hO hD hF g1 g2 hg1 hg2 L hL K hK
  refine ⟨C,hC,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx beta hb hH8 hsmall l i j k F G
  let n := ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖*
    ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x‖
  have hbpos : 0 < beta := lt_of_lt_of_le zero_lt_one hb
  have hn : 0 ≤ n := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hPair (w : List (Fin 3)) (hw : w.length ≤ 2) :
      |⟪coordinateFieldWordPartial w (nativeVReferenceFirstAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p l i) x
        (coreWeightOperator hO hD (besselWeight 1) F x),G x⟫_ℝ| ≤ ((C*eps/beta)*beta^w.length)*n := by
    rw [coordinateFieldWordPartial_nativeVReferenceFirst_angular_inner_half hO hD hF g1 g2 hg1 L lam δ R p l i hg2 hδ hR w F G x]
    have hj := hJet lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx hb hH8 hsmall l i w hw
    have ht := (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right
      ((coordinateFieldWordPartial w (nativeVReferenceFirstBalancedAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p l i) x).le_of_opNorm_le hj
        (coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x))
      (norm_nonneg (coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x)))
    simpa only [n,mul_assoc] using ht
  have h0 := hPair [] (by simp)
  have h1 := hPair [j] (by simp)
  have h2 := hPair [j,k] (by simp)
  have hfirst : (C*eps/beta)*beta=C*eps := div_mul_cancel₀ _ hbpos.ne'
  have hsecond : (C*eps/beta)*beta^2=C*eps*beta := by rw [pow_two,← mul_assoc,hfirst]
  refine ⟨?_,?_,?_⟩
  · rw [nativeVReferenceFirst_angularCoefficient_apply hO hD hF g1 g2 hg1 L lam δ R p l i hg2 hδ hR F x]
    simpa only [coordinateFieldWordPartial,List.length_nil,pow_zero,mul_one,n,mul_assoc] using h0
  · rw [coefficientDerivative_nativeVReferenceFirst_angular_apply hO hD hF g1 g2 hg1 L lam δ R p l i hg2 hδ hR (coordinateDirection j) F x]
    simpa only [coordinateFieldWordPartial,List.length_cons,List.length_nil,Nat.reduceAdd,pow_one,hfirst,n,mul_assoc] using h1
  · rw [coefficientDerivative_second_nativeVReferenceFirst_angular_apply hO hD hF g1 g2 hg1 L lam δ R p l i hg2 hδ hR (coordinateDirection j) (coordinateDirection k) F x]
    simpa only [coordinateFieldWordPartial,List.length_cons,List.length_nil,Nat.reduceAdd,hsecond,n,mul_assoc] using h2

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
