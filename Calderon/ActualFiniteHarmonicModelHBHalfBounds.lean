import Calderon.ActualFiniteHarmonicModelHBFirstAngularWords
import Calderon.ActualFiniteHarmonicModelFirstAngularCoefficientBounds
import Calderon.ActualFiniteHarmonicModelDerivativeRaisingCommutator

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph BalancedAngularShift
  ActualPhysicalMixedFirst ActualScalarPrincipalAdjoint ActualNormalizedSecondModelErrorAssembly
  ReferenceWeightedApproximation CoordinateBootstrapJets ReferenceDensityBounds NormalizedPrincipalMetric
  SmoothMetricFrame MovingFrameConnection ConformalDepth ActualMixedDensityHigherCoefficientJets
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev nativeHBHalfBoundsFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] nativeHBHalfBoundsFunction
theorem exists_nativeH_nativeB_commutator_uniform_half_bound
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
      ∀ l i : Fin 3, ∀ F G : smoothCompactFiniteSphereCore hO hD,
      |⟪(ActualModelCommutatorWords.commutator
          (nativeH hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR l)
          (nativeB hO hD hF g1 g2 hg1 L lam δ R p i hg2 hδ hR)) F x,G x⟫_ℝ| ≤
        (C * eps / beta) * ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖ *
          ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x‖ := by
  obtain ⟨C1,hC1,hCoeff⟩ := exists_native_first_angular_coefficients_uniform_bounds g1 g2 hg1 hg2 L hL K hK
  obtain ⟨M,hM,hbackground⟩ := exists_mixed_background_coordinate_jet_bound g1 hg1 L K hK 0
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  let C0 : ℝ := 1+C1+2*M
  have hC0 : 0 < C0 := by dsimp only [C0]; positivity
  have hC10 : C1 ≤ C0 := by dsimp only [C0]; linarith
  have hC1M0 : C1+2*M ≤ C0 := by dsimp only [C0]; linarith
  let C : ℝ := 1+165*C0^2+162*C0^3
  have hC00 : 0 ≤ C0 := hC0.le
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C,hC,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx beta hb hH8 hsmall l i F G
  let r := referenceRadius δ R p L x
  let Rate := eps/beta
  let UF := coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x
  let VG := coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x
  let n := ‖UF‖*‖VG‖
  let m (a j : Fin 3) := physicalMixedFirstCoefficient g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a j x
  let f (a : Fin 3) := m a l+2*referenceMetricGramFrame g1 L (lam,x) a l
  let d (j : Fin 3) := nativeFirstDegreeCoefficient g1 g2 L lam δ R p j x
  let k (j c : Fin 3) := nativeFirstConnectionCoefficient g1 g2 L lam δ R p j c x
  let Gamma (c b a : Fin 3) := referenceFrameConnectionCoefficient g1 L lam x (referenceMetricGramFrame g1 L (lam,x) c) b a
  let D (a : Fin 3) := ⟪coreDerivative hO hD hF a F x,G x⟫_ℝ
  let Rv (a : Fin 3) := ⟪coreRaising hO hD hF a F x,G x⟫_ℝ
  let DR (a b : Fin 3) := ⟪(ActualModelCommutatorWords.commutator (coreDerivative hO hD hF a)
    (coreRaising hO hD hF b)) F x,G x⟫_ℝ
  have hr : 0 < r := referenceRadius_pos δ R p L x hδ hR
  have hbpos : 0 < beta := lt_of_lt_of_le zero_lt_one hb
  have hb0 : 0 ≤ beta := hbpos.le
  have hRate : 0 ≤ Rate := div_nonneg heps hb0
  have hn : 0 ≤ n := mul_nonneg (norm_nonneg UF) (norm_nonneg VG)
  change r*beta^2 ≤ eps at hsmall
  have hr1 : r ≤ 1 := ((le_mul_of_one_le_right hr.le (one_le_pow₀ hb)).trans hsmall).trans heps1
  have hrb : r*beta ≤ eps/beta := (le_div_iff₀ hbpos).2 (by simpa only [pow_two,mul_assoc] using hsmall)
  have hrRate : r ≤ Rate := (le_mul_of_one_le_right hr.le hb).trans hrb
  have her1 : eps*r ≤ 1 := by nlinarith
  have herRate : eps*r ≤ Rate := (mul_le_of_le_one_left hr.le heps1).trans hrRate
  have her2b : eps*r^2*beta ≤ Rate := by
    calc
      eps*r^2*beta = (eps*r)*(r*beta) := by ring
      _ ≤ r*beta := mul_le_of_le_one_left (mul_nonneg hr.le hb0) her1
      _ ≤ Rate := hrb
  have hc (j a b c : Fin 3) := hCoeff lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx hb hH8 hsmall j a b c
  have hm1 (a j : Fin 3) : |m a j| ≤ C1*eps*r := (hc j a 0 0).1
  have hm (a j : Fin 3) : |m a j| ≤ C0*eps*r := (hm1 a j).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC10 heps) hr.le)
  have hd (j : Fin 3) : |d j| ≤ C0*r*beta := ((hc j 0 0 0).2.1).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC10 hr.le) hb0)
  have hk (j c : Fin 3) : |k j c| ≤ C0*r := ((hc j 0 0 c).2.2.1).trans
    (mul_le_mul_of_nonneg_right hC10 hr.le)
  have hGamma (c b a : Fin 3) : |Gamma c b a| ≤ C0 := ((hc 0 a b c).2.2.2).trans hC10
  have hFrame (a j : Fin 3) : |referenceMetricGramFrame g1 L (lam,x) a j| ≤ M := by
    simpa only [ActualReferenceDDHigherGeometryJets.coordinateFieldWordPartial] using (hbackground lam hlam x hx).1 [] (by simp) a j
  have hf (a : Fin 3) : |f a| ≤ C0 := by
    have h2e : |2*referenceMetricGramFrame g1 L (lam,x) a l| ≤ 2*M := by
      rw [abs_mul]
      simpa only [abs_of_pos (by norm_num : (0 : ℝ)<2)] using
        mul_le_mul_of_nonneg_left (hFrame a l) (by norm_num : (0 : ℝ)≤2)
    calc
      _ ≤ |m a l|+|2*referenceMetricGramFrame g1 L (lam,x) a l| := abs_add_le _ _
      _ ≤ C1*eps*r+2*M := add_le_add (hm1 a l) h2e
      _ ≤ C1+2*M := add_le_add (by nlinarith [mul_le_mul_of_nonneg_left her1 hC1.le]) le_rfl
      _ ≤ C0 := hC1M0
  have hDerivative (a : Fin 3) : |D a| ≤ 4*n := by
    have ht := abs_inner_derivative_le_half_norm hF hO hD a (F x) UF (coreDerivative hO hD hF a F x) (G x) VG
      (coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) F x)
      (coreDerivative_graph hO hD hF a F x)
      (coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) G x)
    simpa only [D,n,mul_assoc] using ht
  have hRaising (a : Fin 3) : |Rv a| ≤ 2*n := by
    have ht := abs_inner_raising_le_half_norm hF hO hD a (F x) UF (coreRaising hO hD hF a F x) (G x) VG
      (coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) F x)
      (coreRaising_graph hO hD hF a F x)
      (coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) G x)
    simpa only [Rv,n,mul_assoc] using ht
  have hDR (a b : Fin 3) : |DR a b| ≤ 15*n := by
    simpa only [DR,n,UF,VG,mul_assoc] using abs_inner_coreDerivative_coreRaising_commutator_le_half hO hD hF a b F G x
  have hMinus (a : Fin 3) : |D a-Rv a| ≤ 6*n := by
    have ht : |D a-Rv a| ≤ |D a|+|Rv a| := by
      simpa only [sub_eq_add_neg,abs_neg] using abs_add_le (D a) (-Rv a)
    exact ht.trans (by linarith [hDerivative a,hRaising a])
  have hPlus (a : Fin 3) : |D a+Rv a| ≤ 6*n :=
    (abs_add_le _ _).trans (by linarith [hDerivative a,hRaising a])
  have hDegreeCoeff (a : Fin 3) : |d i*f a| ≤ C0^2*Rate := by
    rw [abs_mul]
    calc
      _ ≤ (C0*r*beta)*C0 := mul_le_mul (hd i) (hf a) (abs_nonneg _) (by positivity)
      _ = C0^2*(r*beta) := by ring
      _ ≤ C0^2*Rate := mul_le_mul_of_nonneg_left hrb (sq_nonneg C0)
  have hConnectionCoeff (c a b : Fin 3) : |k i c*f a*Gamma c b a| ≤ C0^3*Rate := by
    rw [abs_mul,abs_mul]
    calc
      _ ≤ ((C0*r)*C0)*C0 := mul_le_mul
        (mul_le_mul (hk i c) (hf a) (abs_nonneg _) (by positivity)) (hGamma c b a) (abs_nonneg _) (by positivity)
      _ = C0^3*r := by ring
      _ ≤ C0^3*Rate := mul_le_mul_of_nonneg_left hrRate (pow_nonneg hC00 _)
  have hRaisingCoeff (b : Fin 3) : |m b i*(2*d l)| ≤ 2*C0^2*Rate := by
    rw [abs_mul]
    have h2d : |2*d l| ≤ 2*(C0*r*beta) := by
      rw [abs_mul]
      simpa only [abs_of_pos (by norm_num : (0 : ℝ)<2)] using mul_le_mul_of_nonneg_left (hd l) (by norm_num : (0 : ℝ)≤2)
    calc
      _ ≤ (C0*eps*r)*(2*(C0*r*beta)) := mul_le_mul (hm b i) h2d (abs_nonneg _) (by positivity)
      _ = (2*C0^2)*(eps*r^2*beta) := by ring
      _ ≤ (2*C0^2)*Rate := mul_le_mul_of_nonneg_left her2b (by positivity)
  have hDRCoeff (b a : Fin 3) : |m b i*f a| ≤ C0^2*Rate := by
    rw [abs_mul]
    calc
      _ ≤ (C0*eps*r)*C0 := mul_le_mul (hm b i) (hf a) (abs_nonneg _) (by positivity)
      _ = C0^2*(eps*r) := by ring
      _ ≤ C0^2*Rate := mul_le_mul_of_nonneg_left herRate (sq_nonneg C0)
  have hDegreeTerm (a : Fin 3) : |d i*f a*(D a-Rv a)| ≤ (6*C0^2)*Rate*n := by
    rw [abs_mul]
    calc
      _ ≤ (C0^2*Rate)*(6*n) := mul_le_mul (hDegreeCoeff a) (hMinus a) (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hConnectionTerm (c a b : Fin 3) : |k i c*f a*Gamma c b a*(D b+Rv b)| ≤ (6*C0^3)*Rate*n := by
    rw [abs_mul]
    calc
      _ ≤ (C0^3*Rate)*(6*n) := mul_le_mul (hConnectionCoeff c a b) (hPlus b) (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hRaisingTerm (b : Fin 3) : |m b i*(2*d l)*Rv b| ≤ (4*C0^2)*Rate*n := by
    rw [abs_mul]
    calc
      _ ≤ (2*C0^2*Rate)*(2*n) := mul_le_mul (hRaisingCoeff b) (hRaising b) (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hDRTerm (b a : Fin 3) : |m b i*f a*DR a b| ≤ (15*C0^2)*Rate*n := by
    rw [abs_mul]
    calc
      _ ≤ (C0^2*Rate)*(15*n) := mul_le_mul (hDRCoeff b a) (hDR a b) (abs_nonneg _) (by positivity)
      _ = _ := by ring
  let deg : ℝ := ∑ a : Fin 3, d i*f a*(D a-Rv a)
  let conn : ℝ := ∑ c : Fin 3, ∑ a : Fin 3, ∑ b : Fin 3, k i c*f a*Gamma c b a*(D b+Rv b)
  let raise : ℝ := ∑ b : Fin 3, m b i*(2*d l)*Rv b
  let dr : ℝ := ∑ b : Fin 3, ∑ a : Fin 3, m b i*f a*DR a b
  have hdeg : |deg| ≤ (18*C0^2)*Rate*n := by
    calc
      _ ≤ ∑ a : Fin 3, |d i*f a*(D a-Rv a)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a : Fin 3, (6*C0^2)*Rate*n := Finset.sum_le_sum (fun a _ => hDegreeTerm a)
      _ = _ := by simp only [Fin.sum_univ_three]; ring
  have hconn : |conn| ≤ (162*C0^3)*Rate*n := by
    have hs : |conn| ≤ ∑ c : Fin 3, ∑ a : Fin 3, ∑ b : Fin 3, |k i c*f a*Gamma c b a*(D b+Rv b)| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun c _ =>
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun a _ => Finset.abs_sum_le_sum_abs _ _))))
    calc
      _ ≤ ∑ c : Fin 3, ∑ a : Fin 3, ∑ b : Fin 3, |k i c*f a*Gamma c b a*(D b+Rv b)| := hs
      _ ≤ ∑ c : Fin 3, ∑ a : Fin 3, ∑ b : Fin 3, (6*C0^3)*Rate*n := Finset.sum_le_sum (fun c _ =>
        Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => hConnectionTerm c a b)))
      _ = _ := by simp only [Fin.sum_univ_three]; ring
  have hraise : |raise| ≤ (12*C0^2)*Rate*n := by
    calc
      _ ≤ ∑ b : Fin 3, |m b i*(2*d l)*Rv b| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ b : Fin 3, (4*C0^2)*Rate*n := Finset.sum_le_sum (fun b _ => hRaisingTerm b)
      _ = _ := by simp only [Fin.sum_univ_three]; ring
  have hdr : |dr| ≤ (135*C0^2)*Rate*n := by
    have hs : |dr| ≤ ∑ b : Fin 3, ∑ a : Fin 3, |m b i*f a*DR a b| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun b _ => Finset.abs_sum_le_sum_abs _ _))
    calc
      _ ≤ ∑ b : Fin 3, ∑ a : Fin 3, |m b i*f a*DR a b| := hs
      _ ≤ ∑ b : Fin 3, ∑ a : Fin 3, (15*C0^2)*Rate*n :=
        Finset.sum_le_sum (fun b _ => Finset.sum_le_sum (fun a _ => hDRTerm b a))
      _ = _ := by simp only [Fin.sum_univ_three]; ring
  have hexp := congrArg (fun T : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) => ⟪T F x,G x⟫_ℝ)
    (nativeH_nativeB_commutator_eq_first_angular_words hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR l i)
  dsimp only at hexp
  simp only [LinearMap.add_apply,LinearMap.sub_apply,LinearMap.neg_apply,LinearMap.sum_apply,LinearMap.smul_apply,
    Module.End.mul_apply,coreScalar,nativeReferenceFrameScalar,LinearMap.coe_mk,AddHom.coe_mk,Submodule.coe_mk,Submodule.coe_add,
    Submodule.coe_sub,Submodule.coe_neg,Submodule.coe_smul,Submodule.coe_sum,Finset.sum_apply,
    Pi.add_apply,Pi.sub_apply,Pi.neg_apply,Pi.smul_apply,smul_smul,add_smul,inner_neg_left,inner_add_left,inner_sub_left,
    real_inner_smul_left,sum_inner,mul_assoc] at hexp
  have hform : ⟪(ActualModelCommutatorWords.commutator
      (nativeH hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR l)
      (nativeB hO hD hF g1 g2 hg1 L lam δ R p i hg2 hδ hR)) F x,G x⟫_ℝ = -deg+conn-raise-dr := by
    have hDegreeCollection (A B C D : Fin 3 → ℝ) :
        (∑ a : Fin 3, ((A a-B a)+(C a-D a))) =
          ∑ a : Fin 3, ((A a+C a)-(B a+D a)) := by
      apply Finset.sum_congr rfl
      intro a ha
      ring
    have hConnectionCollection (A B C D : Fin 3 → Fin 3 → Fin 3 → ℝ) :
        (∑ c : Fin 3, ∑ a : Fin 3, ∑ b : Fin 3, ((A c a b+B c a b)+(C c a b+D c a b))) =
          ∑ c : Fin 3, ∑ a : Fin 3, ∑ b : Fin 3, ((A c a b+C c a b)+(B c a b+D c a b)) := by
      apply Finset.sum_congr rfl
      intro c hc
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      ring
    simp only [deg,conn,raise,dr,m,f,d,k,Gamma,D,Rv,DR,mul_assoc,add_mul,mul_add,mul_sub] at hexp ⊢
    rw [hDegreeCollection,hConnectionCollection] at hexp
    exact hexp
  rw [hform]
  have htriangle : |-deg+conn-raise-dr| ≤ |deg|+|conn|+|raise|+|dr| := by
    calc
      _ ≤ |-deg+conn-raise|+|dr| := by simpa only [sub_eq_add_neg,abs_neg] using abs_add_le (-deg+conn-raise) (-dr)
      _ ≤ (|-deg+conn|+|raise|)+|dr| := add_le_add
        (by simpa only [sub_eq_add_neg,abs_neg] using abs_add_le (-deg+conn) (-raise)) le_rfl
      _ ≤ ((|deg|+|conn|)+|raise|)+|dr| := add_le_add (add_le_add
        (by simpa only [abs_neg] using abs_add_le (-deg) conn) le_rfl) le_rfl
  calc
    _ ≤ |deg|+|conn|+|raise|+|dr| := htriangle
    _ ≤ (18*C0^2)*Rate*n+(162*C0^3)*Rate*n+(12*C0^2)*Rate*n+(135*C0^2)*Rate*n :=
      add_le_add (add_le_add (add_le_add hdeg hconn) hraise) hdr
    _ = (165*C0^2+162*C0^3)*Rate*n := by ring
    _ ≤ C*Rate*n := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by dsimp only [C]; linarith) hRate) hn
    _ = _ := by dsimp only [C,Rate,n,UF,VG]; ring

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
