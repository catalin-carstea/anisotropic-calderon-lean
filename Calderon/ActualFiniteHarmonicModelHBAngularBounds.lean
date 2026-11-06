import Calderon.ActualFiniteHarmonicModelHBAngularJets
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
private abbrev nativeHBQuantFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] nativeHBQuantFunction
theorem exists_nativeHBBalancedAngularCoefficient_uniform_coordinate_word_bound
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
      ‖coordinateFieldWordPartial w (nativeHBBalancedAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p l i) x‖ ≤
        (C * eps / beta) * beta^w.length := by
  obtain ⟨C0,hC0,hCoeff⟩ := exists_native_first_angular_coefficients_uniform_coordinate_word_bounds g1 g2 hg1 hg2 L hL K hK
  let C : ℝ := 1+2640*C0^2+10368*C0^3
  have hC00 : 0 ≤ C0 := hC0.le
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C,hC,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx beta hb hH8 hsmall l i w hw
  let r := referenceRadius δ R p L x
  let Rate := eps/beta
  let m (a j : Fin 3) := physicalMixedFirstCoefficient g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a j
  let f (a : Fin 3) (y : R3) := m a l y+2*referenceMetricGramFrame g1 L (lam,y) a l
  let d (j : Fin 3) := nativeFirstDegreeCoefficient g1 g2 L lam δ R p j
  let k (j c : Fin 3) := nativeFirstConnectionCoefficient g1 g2 L lam δ R p j c
  let Gamma (c b a : Fin 3) (y : R3) := referenceFrameConnectionCoefficient g1 L lam y
    (referenceMetricGramFrame g1 L (lam,y) c) b a
  let DM (a : Fin 3) := balancedDerivative hF hO hD a-balancedRaising hF hO hD a
  let DP (a : Fin 3) := balancedDerivative hF hO hD a+balancedRaising hF hO hD a
  let Rop (a : Fin 3) := balancedRaising hF hO hD a
  let DR (a b : Fin 3) := normalizedDerivativeRaisingCommutator hF hO hD a b
  have hr : 0 < r := referenceRadius_pos δ R p L x hδ hR
  have hbpos : 0 < beta := lt_of_lt_of_le zero_lt_one hb
  have hb0 : 0 ≤ beta := hbpos.le
  have hRate : 0 ≤ Rate := div_nonneg heps hb0
  change r*beta^2 ≤ eps at hsmall
  have hr1 : r ≤ 1 := ((le_mul_of_one_le_right hr.le (one_le_pow₀ hb)).trans hsmall).trans heps1
  have her1 : eps*r ≤ 1 := by nlinarith
  have hrb : r*beta ≤ Rate := (le_div_iff₀ hbpos).2 (by simpa only [pow_two,mul_assoc] using hsmall)
  have hrRate : r ≤ Rate := (le_mul_of_one_le_right hr.le hb).trans hrb
  have herRate : eps*r ≤ Rate := (mul_le_of_le_one_left hr.le heps1).trans hrRate
  have her2b : eps*r^2*beta ≤ Rate := by
    calc
      eps*r^2*beta = (eps*r)*(r*beta) := by ring
      _ ≤ r*beta := mul_le_of_le_one_left (mul_nonneg hr.le hb0) her1
      _ ≤ Rate := hrb
  have hmS (a j : Fin 3) : ContDiff ℝ ∞ (m a j) := contDiff_physicalMixedFirstCoefficient g1 hg1 L lam _
    (fun u v => contDiff_referenceNormalizedPrincipalDifference_entry g1 g2 hg1 hg2 L lam u v) a j
  have hfS (a : Fin 3) : ContDiff ℝ ∞ (f a) := (hmS a l).add (contDiff_const.mul
    ((contDiff_piLp_apply (p := 2) (i := l) : ContDiff ℝ ∞ (fun z : R3 => z l)).comp
      (contDiff_referenceMetricGramFrame_slice g1 hg1 L lam a)))
  have hdS (j : Fin 3) := contDiff_nativeFirstDegreeCoefficient g1 g2 hg1 hg2 L lam δ R p hδ hR j
  have hkS (j c : Fin 3) := contDiff_nativeFirstConnectionCoefficient g1 g2 hg1 hg2 L lam δ R p hδ hR j c
  have hGammaS (c b a : Fin 3) : ContDiff ℝ ∞ (Gamma c b a) :=
    contDiff_referenceFrameConnectionCoefficient_field g1 hg1 L lam _
      (contDiff_referenceMetricGramFrame_slice g1 hg1 L lam c) b a
  have hc (v : List (Fin 3)) (hv : v.length ≤ 2) (j a b c : Fin 3) :=
    hCoeff lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx hb hH8 hsmall v hv j a b c
  have hmj (a j : Fin 3) : HasCoordinateWordJetBound 2 (m a j) x (C0*eps*r) beta 0 := by
    intro v hv
    simpa only [Real.norm_eq_abs,Nat.zero_add,m,mul_assoc] using (hc v hv j a 0 0).1
  have hfj (a : Fin 3) : HasCoordinateWordJetBound 2 (f a) x C0 beta 0 := by
    intro v hv
    simpa only [Real.norm_eq_abs,Nat.zero_add,f,m] using (hc v hv l a 0 0).2.1
  have hdj (j : Fin 3) : HasCoordinateWordJetBound 2 (d j) x (C0*r) beta 1 := by
    intro v hv
    simpa only [Real.norm_eq_abs,d,mul_assoc] using (hc v hv j 0 0 0).2.2.1
  have hkj (j c : Fin 3) : HasCoordinateWordJetBound 2 (k j c) x (C0*r) beta 0 := by
    intro v hv
    simpa only [Real.norm_eq_abs,Nat.zero_add,k,mul_assoc] using (hc v hv j 0 0 c).2.2.2.1
  have hGammaj (c b a : Fin 3) : HasCoordinateWordJetBound 2 (Gamma c b a) x C0 beta 0 := by
    intro v hv
    simpa only [Real.norm_eq_abs,Nat.zero_add,Gamma] using (hc v hv 0 a b c).2.2.2.2.1
  have hDM (a : Fin 3) : ‖DM a‖ ≤ 6 := (norm_sub_le _ _).trans
    (by linarith [norm_balancedDerivative_le hF hO hD a,norm_balancedRaising_le hF hO hD a])
  have hDP (a : Fin 3) : ‖DP a‖ ≤ 6 := (norm_add_le _ _).trans
    (by linarith [norm_balancedDerivative_le hF hO hD a,norm_balancedRaising_le hF hO hD a])
  have hRop (a : Fin 3) : ‖Rop a‖ ≤ 2 := norm_balancedRaising_le hF hO hD a
  have hDR (a b : Fin 3) : ‖DR a b‖ ≤ 15 := norm_normalizedDerivativeRaisingCommutator_le hF hO hD a b
  have hFixed (z : R3 → ℝ) (hz : ContDiff ℝ ∞ z) (S : SphereL2 →L[ℝ] SphereL2)
      (B M : ℝ) (s : ℕ) (hB : 0 ≤ B) (hM : 0 ≤ M) (hS : ‖S‖ ≤ M)
      (hj : HasCoordinateWordJetBound 2 z x B beta s) :
      HasCoordinateWordJetBound 2 (fun y => z y • S) x (4*B*M) beta s := by
    have hSj := hasCoordinateWordJetBound_const_normed 2 S x M beta hS hb0
    have ht := hasCoordinateWordJetBound_smul 2 z (fun _ : R3 => S) hz contDiff_const
      x B M beta s 0 hB hM hb0 hj hSj
    simpa only [show (2:ℝ)^2=4 by norm_num,Nat.add_zero] using ht
  have hDegScalar (a : Fin 3) : HasCoordinateWordJetBound 2 (fun y => d i y*f a y)
      x (4*C0^2*r) beta 1 := by
    have ht := hasCoordinateWordJetBound_mul 2 (d i) (f a) (hdS i) (hfS a)
      x (C0*r) C0 beta 1 0 (mul_nonneg hC00 hr.le) hC00 hb0 (hdj i) (hfj a)
    convert ht using 1 <;> simp only [show (2:ℝ)^2=4 by norm_num,Nat.add_zero] <;> ring
  have hConnScalar (c a b : Fin 3) : HasCoordinateWordJetBound 2
      (fun y => k i c y*f a y*Gamma c b a y) x (16*C0^3*r) beta 0 := by
    have hp := hasCoordinateWordJetBound_mul 2 (k i c) (f a) (hkS i c) (hfS a)
      x (C0*r) C0 beta 0 0 (mul_nonneg hC00 hr.le) hC00 hb0 (hkj i c) (hfj a)
    have ht := hasCoordinateWordJetBound_mul 2 (fun y => k i c y*f a y) (Gamma c b a)
      ((hkS i c).mul (hfS a)) (hGammaS c b a) x ((2:ℝ)^2*(C0*r)*C0) C0 beta 0 0
      (by positivity) hC00 hb0 hp (hGammaj c b a)
    convert ht using 1 <;> simp only [show (2:ℝ)^2=4 by norm_num,Nat.zero_add] <;> ring
  have hRaiseScalar (b : Fin 3) : HasCoordinateWordJetBound 2 (fun y => m b i y*(2*d l y))
      x (8*C0^2*eps*r^2) beta 1 := by
    have h2d : HasCoordinateWordJetBound 2 (fun y => 2*d l y) x (2*C0*r) beta 1 := by
      intro v hv
      rw [ActualMixedDensityHigherCoefficientJets.coordinateFieldWordPartial_const_mul v 2 _ (hdS l),Real.norm_eq_abs,abs_mul]
      simpa only [Real.norm_eq_abs,show |(2:ℝ)|=2 by norm_num,mul_assoc] using
        mul_le_mul_of_nonneg_left (hdj l v hv) (by norm_num : (0:ℝ)≤2)
    have ht := hasCoordinateWordJetBound_mul 2 (m b i) (fun y => 2*d l y) (hmS b i)
      (contDiff_const.mul (hdS l)) x (C0*eps*r) (2*C0*r) beta 0 1
      (by positivity) (by positivity) hb0 (hmj b i) h2d
    convert ht using 1 <;> simp only [show (2:ℝ)^2=4 by norm_num,Nat.zero_add] <;> ring
  have hDRScalar (b a : Fin 3) : HasCoordinateWordJetBound 2 (fun y => m b i y*f a y)
      x (4*C0^2*eps*r) beta 0 := by
    have ht := hasCoordinateWordJetBound_mul 2 (m b i) (f a) (hmS b i) (hfS a)
      x (C0*eps*r) C0 beta 0 0 (by positivity) hC00 hb0 (hmj b i) (hfj a)
    convert ht using 1 <;> simp only [show (2:ℝ)^2=4 by norm_num,Nat.zero_add] <;> ring
  let FD (y : R3) := ∑ a : Fin 3, (d i y*f a y) • DM a
  let FC (y : R3) := ∑ c : Fin 3, ∑ a : Fin 3, ∑ b : Fin 3,
    (k i c y*f a y*Gamma c b a y) • DP b
  let FR (y : R3) := ∑ b : Fin 3, (m b i y*(2*d l y)) • Rop b
  let FDR (y : R3) := ∑ b : Fin 3, ∑ a : Fin 3, (m b i y*f a y) • DR a b
  have hFDS : ContDiff ℝ ∞ FD := ContDiff.sum (fun a _ => ((hdS i).mul (hfS a)).smul contDiff_const)
  have hFCS : ContDiff ℝ ∞ FC := ContDiff.sum (fun c _ => ContDiff.sum (fun a _ => ContDiff.sum (fun b _ =>
    (((hkS i c).mul (hfS a)).mul (hGammaS c b a)).smul contDiff_const)))
  have hFRS : ContDiff ℝ ∞ FR := ContDiff.sum (fun b _ => ((hmS b i).mul (contDiff_const.mul (hdS l))).smul contDiff_const)
  have hFDRS : ContDiff ℝ ∞ FDR := ContDiff.sum (fun b _ => ContDiff.sum (fun a _ => ((hmS b i).mul (hfS a)).smul contDiff_const))
  have hDj (a : Fin 3) : HasCoordinateWordJetBound 2 (fun y => (d i y*f a y) • DM a)
      x (96*C0^2*r) beta 1 := by
    have ht := hFixed (fun y => d i y*f a y) ((hdS i).mul (hfS a)) (DM a)
      (4*C0^2*r) 6 1 (by positivity) (by norm_num) (hDM a) (hDegScalar a)
    convert ht using 1 <;> ring
  have hCj (c a b : Fin 3) : HasCoordinateWordJetBound 2
      (fun y => (k i c y*f a y*Gamma c b a y) • DP b) x (384*C0^3*r) beta 0 := by
    have ht := hFixed _ (((hkS i c).mul (hfS a)).mul (hGammaS c b a)) (DP b)
      (16*C0^3*r) 6 0 (by positivity) (by norm_num) (hDP b) (hConnScalar c a b)
    convert ht using 1 <;> ring
  have hRj (b : Fin 3) : HasCoordinateWordJetBound 2 (fun y => (m b i y*(2*d l y)) • Rop b)
      x (64*C0^2*eps*r^2) beta 1 := by
    have ht := hFixed _ ((hmS b i).mul (contDiff_const.mul (hdS l))) (Rop b)
      (8*C0^2*eps*r^2) 2 1 (by positivity) (by norm_num) (hRop b) (hRaiseScalar b)
    convert ht using 1 <;> ring
  have hDRj (b a : Fin 3) : HasCoordinateWordJetBound 2 (fun y => (m b i y*f a y) • DR a b)
      x (240*C0^2*eps*r) beta 0 := by
    have ht := hFixed _ ((hmS b i).mul (hfS a)) (DR a b)
      (4*C0^2*eps*r) 15 0 (by positivity) (by norm_num) (hDR a b) (hDRScalar b a)
    convert ht using 1 <;> ring
  have hDsum : HasCoordinateWordJetBound 2 FD x (288*C0^2*r) beta 1 := by
    have ht := hasCoordinateWordJetBound_sum 2 (fun a : Fin 3 => fun y => (d i y*f a y) • DM a)
      (fun a => ((hdS i).mul (hfS a)).smul contDiff_const) x (96*C0^2*r) beta 1 hDj
    convert ht using 1 <;> simp only [Fintype.card_fin,Nat.cast_ofNat] <;> ring
  have hCsum : HasCoordinateWordJetBound 2 FC x (10368*C0^3*r) beta 0 := by
    have hBsum (c a : Fin 3) : HasCoordinateWordJetBound 2
        (fun y => ∑ b : Fin 3, (k i c y*f a y*Gamma c b a y) • DP b) x (1152*C0^3*r) beta 0 := by
      have ht := hasCoordinateWordJetBound_sum 2
        (fun b : Fin 3 => fun y => (k i c y*f a y*Gamma c b a y) • DP b)
        (fun b => (((hkS i c).mul (hfS a)).mul (hGammaS c b a)).smul contDiff_const)
        x (384*C0^3*r) beta 0 (hCj c a)
      convert ht using 1 <;> simp only [Fintype.card_fin,Nat.cast_ofNat] <;> ring
    have hAsum (c : Fin 3) : HasCoordinateWordJetBound 2
        (fun y => ∑ a : Fin 3, ∑ b : Fin 3, (k i c y*f a y*Gamma c b a y) • DP b) x (3456*C0^3*r) beta 0 := by
      have ht := hasCoordinateWordJetBound_sum 2
        (fun a : Fin 3 => fun y => ∑ b : Fin 3, (k i c y*f a y*Gamma c b a y) • DP b)
        (fun a => ContDiff.sum (fun b _ => (((hkS i c).mul (hfS a)).mul (hGammaS c b a)).smul contDiff_const))
        x (1152*C0^3*r) beta 0 (hBsum c)
      convert ht using 1 <;> simp only [Fintype.card_fin,Nat.cast_ofNat] <;> ring
    have ht := hasCoordinateWordJetBound_sum 2
      (fun c : Fin 3 => fun y => ∑ a : Fin 3, ∑ b : Fin 3, (k i c y*f a y*Gamma c b a y) • DP b)
      (fun c => ContDiff.sum (fun a _ => ContDiff.sum (fun b _ => (((hkS i c).mul (hfS a)).mul (hGammaS c b a)).smul contDiff_const)))
      x (3456*C0^3*r) beta 0 hAsum
    convert ht using 1 <;> simp only [Fintype.card_fin,Nat.cast_ofNat] <;> ring
  have hRsum : HasCoordinateWordJetBound 2 FR x (192*C0^2*eps*r^2) beta 1 := by
    have ht := hasCoordinateWordJetBound_sum 2
      (fun b : Fin 3 => fun y => (m b i y*(2*d l y)) • Rop b)
      (fun b => ((hmS b i).mul (contDiff_const.mul (hdS l))).smul contDiff_const)
      x (64*C0^2*eps*r^2) beta 1 hRj
    convert ht using 1 <;> simp only [Fintype.card_fin,Nat.cast_ofNat] <;> ring
  have hDRsum : HasCoordinateWordJetBound 2 FDR x (2160*C0^2*eps*r) beta 0 := by
    have hAsum (b : Fin 3) : HasCoordinateWordJetBound 2
        (fun y => ∑ a : Fin 3, (m b i y*f a y) • DR a b) x (720*C0^2*eps*r) beta 0 := by
      have ht := hasCoordinateWordJetBound_sum 2
        (fun a : Fin 3 => fun y => (m b i y*f a y) • DR a b)
        (fun a => ((hmS b i).mul (hfS a)).smul contDiff_const) x (240*C0^2*eps*r) beta 0 (hDRj b)
      convert ht using 1 <;> simp only [Fintype.card_fin,Nat.cast_ofNat] <;> ring
    have ht := hasCoordinateWordJetBound_sum 2
      (fun b : Fin 3 => fun y => ∑ a : Fin 3, (m b i y*f a y) • DR a b)
      (fun b => ContDiff.sum (fun a _ => ((hmS b i).mul (hfS a)).smul contDiff_const))
      x (720*C0^2*eps*r) beta 0 hAsum
    convert ht using 1 <;> simp only [Fintype.card_fin,Nat.cast_ofNat] <;> ring
  have hDsmall : HasCoordinateWordJetBound 2 FD x ((288*C0^2)*Rate) beta 0 := by
    intro v hv
    simp only [Nat.zero_add]
    calc
      _ ≤ (288*C0^2*r)*beta^(1+v.length) := hDsum v hv
      _ = (288*C0^2)*(r*beta)*beta^v.length := by rw [pow_add]; ring
      _ ≤ ((288*C0^2)*Rate)*beta^v.length := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hrb (by positivity)) (pow_nonneg hb0 _)
  have hCsmall : HasCoordinateWordJetBound 2 FC x ((10368*C0^3)*Rate) beta 0 := by
    intro v hv
    simp only [Nat.zero_add]
    calc
      _ ≤ (10368*C0^3*r)*beta^v.length := by simpa only [Nat.zero_add] using hCsum v hv
      _ ≤ ((10368*C0^3)*Rate)*beta^v.length := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hrRate (by positivity)) (pow_nonneg hb0 _)
  have hRsmall : HasCoordinateWordJetBound 2 FR x ((192*C0^2)*Rate) beta 0 := by
    intro v hv
    simp only [Nat.zero_add]
    calc
      _ ≤ (192*C0^2*eps*r^2)*beta^(1+v.length) := hRsum v hv
      _ = (192*C0^2)*(eps*r^2*beta)*beta^v.length := by rw [pow_add]; ring
      _ ≤ ((192*C0^2)*Rate)*beta^v.length := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left her2b (by positivity)) (pow_nonneg hb0 _)
  have hDRsmall : HasCoordinateWordJetBound 2 FDR x ((2160*C0^2)*Rate) beta 0 := by
    intro v hv
    simp only [Nat.zero_add]
    calc
      _ ≤ (2160*C0^2*eps*r)*beta^v.length := by simpa only [Nat.zero_add] using hDRsum v hv
      _ = (2160*C0^2)*(eps*r)*beta^v.length := by ring
      _ ≤ ((2160*C0^2)*Rate)*beta^v.length := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left herRate (by positivity)) (pow_nonneg hb0 _)
  have hnD := hasCoordinateWordJetBound_neg 2 FD hFDS x ((288*C0^2)*Rate) beta 0 hDsmall
  have ha := hasCoordinateWordJetBound_add 2 (fun y => -FD y) FC hFDS.neg hFCS
    x ((288*C0^2)*Rate) ((10368*C0^3)*Rate) beta 0 hnD hCsmall
  have hs := hasCoordinateWordJetBound_sub 2 (fun y => -FD y+FC y) FR (hFDS.neg.add hFCS) hFRS
    x (((288*C0^2)*Rate)+((10368*C0^3)*Rate)) ((192*C0^2)*Rate) beta 0 ha hRsmall
  have ht := hasCoordinateWordJetBound_sub 2 (fun y => -FD y+FC y-FR y) FDR
    ((hFDS.neg.add hFCS).sub hFRS) hFDRS
    x ((((288*C0^2)*Rate)+((10368*C0^3)*Rate))+((192*C0^2)*Rate)) ((2160*C0^2)*Rate) beta 0 hs hDRsmall
  have htotal : HasCoordinateWordJetBound 2 (nativeHBBalancedAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p l i)
      x ((2640*C0^2+10368*C0^3)*Rate) beta 0 := by
    have hfield : nativeHBBalancedAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p l i =
        (fun y => -FD y+FC y-FR y-FDR y) := by
      funext y
      rfl
    rw [hfield]
    convert ht using 1 <;> ring
  calc
    _ ≤ ((2640*C0^2+10368*C0^3)*Rate)*beta^w.length := by simpa only [Nat.zero_add] using htotal w hw
    _ ≤ (C*Rate)*beta^w.length := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by dsimp only [C]; linarith) hRate) (pow_nonneg hb0 _)
    _ = _ := by dsimp only [Rate]; ring


theorem exists_nativeHB_uniform_half_angular_forms
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
      |⟪(ActualModelCommutatorWords.commutator (nativeH hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR l) (nativeB hO hD hF g1 g2 hg1 L lam δ R p i hg2 hδ hR)) F x,G x⟫_ℝ| ≤ (C * eps / beta) * ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖ *
          ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x‖ ∧
      |⟪ActualModelCommutatorWords.coefficientDerivative (coreDirectionalDerivative hO hD (coordinateDirection j))
        (ActualModelCommutatorWords.commutator (nativeH hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR l) (nativeB hO hD hF g1 g2 hg1 L lam δ R p i hg2 hδ hR)) F x,G x⟫_ℝ| ≤ (C * eps) * ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖ *
          ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x‖ ∧
      |⟪ActualModelCommutatorWords.coefficientDerivative (coreDirectionalDerivative hO hD (coordinateDirection j))
        (ActualModelCommutatorWords.coefficientDerivative (coreDirectionalDerivative hO hD (coordinateDirection k))
          (ActualModelCommutatorWords.commutator (nativeH hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR l) (nativeB hO hD hF g1 g2 hg1 L lam δ R p i hg2 hδ hR))) F x,G x⟫_ℝ| ≤ (C * eps * beta) * ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖ *
          ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x‖ := by
  obtain ⟨C,hC,hJet⟩ := exists_nativeHBBalancedAngularCoefficient_uniform_coordinate_word_bound hO hD hF g1 g2 hg1 hg2 L hL K hK
  refine ⟨C,hC,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx beta hb hH8 hsmall l i j k F G
  let n := ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖*
    ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x‖
  have hbpos : 0 < beta := lt_of_lt_of_le zero_lt_one hb
  have hn : 0 ≤ n := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hPair (w : List (Fin 3)) (hw : w.length ≤ 2) :
      |⟪coordinateFieldWordPartial w (nativeHBAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p l i) x
        (coreWeightOperator hO hD (besselWeight 1) F x),G x⟫_ℝ| ≤ ((C*eps/beta)*beta^w.length)*n := by
    rw [coordinateFieldWordPartial_nativeHB_angular_inner_half hO hD hF g1 g2 hg1 L lam δ R p l i hg2 hδ hR w F G x]
    have hj := hJet lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx hb hH8 hsmall l i w hw
    have ht := (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right
      ((coordinateFieldWordPartial w (nativeHBBalancedAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p l i) x).le_of_opNorm_le hj
        (coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x))
      (norm_nonneg (coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x)))
    simpa only [n,mul_assoc] using ht
  have h0 := hPair [] (by simp)
  have h1 := hPair [j] (by simp)
  have h2 := hPair [j,k] (by simp)
  have hfirst : (C*eps/beta)*beta=C*eps := div_mul_cancel₀ _ hbpos.ne'
  have hsecond : (C*eps/beta)*beta^2=C*eps*beta := by rw [pow_two,← mul_assoc,hfirst]
  refine ⟨?_,?_,?_⟩
  · rw [nativeHB_angularCoefficient_apply hO hD hF g1 g2 hg1 L lam δ R p l i hg2 hδ hR F x]
    simpa only [coordinateFieldWordPartial,List.length_nil,pow_zero,mul_one,n,mul_assoc] using h0
  · rw [coefficientDerivative_nativeHB_angular_apply hO hD hF g1 g2 hg1 L lam δ R p l i hg2 hδ hR (coordinateDirection j) F x]
    simpa only [coordinateFieldWordPartial,List.length_cons,List.length_nil,Nat.reduceAdd,pow_one,hfirst,n,mul_assoc] using h1
  · rw [coefficientDerivative_second_nativeHB_angular_apply hO hD hF g1 g2 hg1 L lam δ R p l i hg2 hδ hR (coordinateDirection j) (coordinateDirection k) F x]
    simpa only [coordinateFieldWordPartial,List.length_cons,List.length_nil,Nat.reduceAdd,hsecond,n,mul_assoc] using h2

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
