import Calderon.ActualFiniteHarmonicModelVAngularCommutators
import Calderon.ActualFiniteHarmonicModelFirstAngularCoefficientBounds
import Calderon.ActualFiniteHarmonicModelDerivativeRaisingCommutator

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph BalancedAngularShift
  ActualPhysicalMixedFirst NormalizedPrincipalMetric NormalizedPrincipalMetricSmooth
  ActualMixedDensityHigherCoefficientJets ReferenceWeightedApproximation CoordinateBootstrapJets
  SmoothMetricFrame ConformalDepth ActualAngularCoefficientCommutator
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev nativeVReferenceFirstFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] nativeVReferenceFirstFunction
lemma nativeV_referenceFirst_commutator_eq_angular_words
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) (l i : Fin 3) :
    let m : Fin 3 → Module.End ℝ (smoothCompactFiniteSphereCore hO hD) := fun a =>
      coreScalar hO hD (physicalMixedFirstCoefficient g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a l)
        (contDiff_physicalMixedFirstCoefficient g1 hg1 L lam _
          (fun j k => contDiff_referenceNormalizedPrincipalDifference_entry g1 g2 hg1 hg2 L lam j k) a l)
    let d := coreScalar hO hD (nativeFirstDegreeCoefficient g1 g2 L lam δ R p l)
      (contDiff_nativeFirstDegreeCoefficient g1 g2 hg1 hg2 L lam δ R p hδ hR l)
    let E (b : Fin 3) := nativeReferenceFrameScalar hO hD g1 hg1 L lam b i
    ActualModelCommutatorWords.commutator (nativeV hO hD hF g1 g2 hg1 L lam δ R p l hg2 hδ hR)
      (nativeReferenceFirstCoefficient hO hD hF g1 hg1 L lam δ R p hδ hR i) =
      -(∑ b : Fin 3, E b*((2 : ℝ) • d)*coreRaising hO hD hF b) -
        ∑ b : Fin 3, ∑ a : Fin 3, E b*m a*
          ActualModelCommutatorWords.commutator (coreDerivative hO hD hF a) (coreRaising hO hD hF b) := by
  dsimp only
  let V := nativeV hO hD hF g1 g2 hg1 L lam δ R p l hg2 hδ hR
  let E (b : Fin 3) := nativeReferenceFrameScalar hO hD g1 hg1 L lam b i
  let m (a : Fin 3) := coreScalar hO hD
    (physicalMixedFirstCoefficient g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a l)
    (contDiff_physicalMixedFirstCoefficient g1 hg1 L lam _
      (fun j k => contDiff_referenceNormalizedPrincipalDifference_entry g1 g2 hg1 hg2 L lam j k) a l)
  let d := coreScalar hO hD (nativeFirstDegreeCoefficient g1 g2 L lam δ R p l)
    (contDiff_nativeFirstDegreeCoefficient g1 g2 hg1 hg2 L lam δ R p hδ hR l)
  have hRE (b : Fin 3) : Commute (coreRaising hO hD hF b) (E b) := by
    unfold E nativeReferenceFrameScalar
    exact scalarCentral_coreRaising hO hD hF b _ _
  have hT : nativeReferenceFirstCoefficient hO hD hF g1 hg1 L lam δ R p hδ hR i =
      ∑ b : Fin 3, E b*coreRaising hO hD hF b := by
    unfold nativeReferenceFirstCoefficient
    exact Finset.sum_congr rfl (fun b _ => (hRE b).eq)
  have hVE (b : Fin 3) : Commute V (E b) := by
    unfold E nativeReferenceFrameScalar
    exact nativeV_scalarCentral hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR l _ _
  have hterm (b : Fin 3) : ActualModelCommutatorWords.commutator V (E b*coreRaising hO hD hF b) =
      -(E b*((2 : ℝ) • d)*coreRaising hO hD hF b) -
        ∑ a : Fin 3, E b*m a*ActualModelCommutatorWords.commutator (coreDerivative hO hD hF a) (coreRaising hO hD hF b) := by
    rw [ActualAngularCoefficientCommutator.commutator_mul_right_of_commute _ _ _ (hVE b),
      nativeV_raising_commutator hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR l b]
    apply LinearMap.ext
    intro F
    apply Subtype.ext
    funext x
    simp only [E,m,d,nativeReferenceFrameScalar,coreScalar,Module.End.mul_apply,
      LinearMap.sub_apply,LinearMap.neg_apply,LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.coe_mk,
      AddHom.coe_mk,Submodule.coe_mk,Submodule.coe_sub,Submodule.coe_neg,Submodule.coe_sum,Submodule.coe_smul,
      Pi.sub_apply,Pi.neg_apply,Pi.smul_apply,Finset.sum_apply,smul_sub,smul_neg,Finset.smul_sum,smul_smul,_root_.mul_assoc]
  rw [hT,ActualModelCommutatorWords.commutator_sum_right]
  have hsum := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun b _ => hterm b)
  apply LinearMap.ext
  intro F
  apply Subtype.ext
  funext x
  have he := congrArg (fun T : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) => T F x) hsum
  simpa only [V,E,m,d,nativeReferenceFrameScalar,coreScalar,Module.End.mul_apply,
    LinearMap.sub_apply,LinearMap.neg_apply,LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.coe_mk,
    AddHom.coe_mk,Submodule.coe_mk,Submodule.coe_sub,Submodule.coe_neg,Submodule.coe_sum,Submodule.coe_smul,
    Pi.sub_apply,Pi.neg_apply,Pi.smul_apply,Finset.sum_apply,smul_sub,smul_neg,Finset.smul_sum,smul_smul,
    Finset.sum_sub_distrib,Finset.sum_neg_distrib,_root_.mul_assoc] using he


theorem exists_nativeV_referenceFirst_commutator_uniform_half_bound
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
          (nativeV hO hD hF g1 g2 hg1 L lam δ R p l hg2 hδ hR)
          (nativeReferenceFirstCoefficient hO hD hF g1 hg1 L lam δ R p hδ hR i)) F x,G x⟫_ℝ| ≤
        (C * eps / beta) * ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖ *
          ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x‖ := by
  obtain ⟨C0,hC0,hCoeff⟩ := exists_native_first_angular_coefficients_uniform_bounds g1 g2 hg1 hg2 L hL K hK
  obtain ⟨M,hM,hbackground⟩ := exists_mixed_background_coordinate_jet_bound g1 hg1 L K hK 0
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  let C : ℝ := 1+147*M*C0
  have hC : 0 < C := by dsimp only [C]; positivity
  have hEnlarge : 147*M*C0 ≤ C := by dsimp only [C]; linarith
  refine ⟨C,hC,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx beta hb hH8 hsmall l i F G
  let r := referenceRadius δ R p L x
  let Rate := eps/beta
  let UF := coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x
  let VG := coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x
  let n := ‖UF‖*‖VG‖
  let m (a : Fin 3) := physicalMixedFirstCoefficient g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a l x
  let d := nativeFirstDegreeCoefficient g1 g2 L lam δ R p l x
  let E (b : Fin 3) := referenceMetricGramFrame g1 L (lam,x) b i
  let Rv (b : Fin 3) := ⟪coreRaising hO hD hF b F x,G x⟫_ℝ
  let DR (a b : Fin 3) := ⟪(ActualModelCommutatorWords.commutator (coreDerivative hO hD hF a)
    (coreRaising hO hD hF b)) F x,G x⟫_ℝ
  have hr : 0 < r := referenceRadius_pos δ R p L x hδ hR
  have hbpos : 0 < beta := lt_of_lt_of_le zero_lt_one hb
  have hRate : 0 ≤ Rate := div_nonneg heps hbpos.le
  have hn : 0 ≤ n := mul_nonneg (norm_nonneg UF) (norm_nonneg VG)
  change r*beta^2 ≤ eps at hsmall
  have hrb : r*beta ≤ Rate := (le_div_iff₀ hbpos).2 (by simpa only [pow_two,mul_assoc] using hsmall)
  have hrRate : r ≤ Rate := (le_mul_of_one_le_right hr.le hb).trans hrb
  have herRate : eps*r ≤ Rate := (mul_le_of_le_one_left hr.le heps1).trans hrRate
  have hE (b : Fin 3) : |E b| ≤ M := by
    simpa only [E,ActualReferenceDDHigherGeometryJets.coordinateFieldWordPartial] using (hbackground lam hlam x hx).1 [] (by simp) b i
  have hd : |d| ≤ C0*r*beta := (hCoeff lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx hb hH8 hsmall l 0 0 0).2.1
  have hm (a : Fin 3) : |m a| ≤ C0*eps*r := (hCoeff lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx hb hH8 hsmall l a 0 0).1
  have hRaising (b : Fin 3) : |Rv b| ≤ 2*n := by
    have ht := abs_inner_raising_le_half_norm hF hO hD b (F x) UF (coreRaising hO hD hF b F x) (G x) VG
      (coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) F x)
      (coreRaising_graph hO hD hF b F x)
      (coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) G x)
    simpa only [Rv,n,mul_assoc] using ht
  have hDR (a b : Fin 3) : |DR a b| ≤ 15*n := by
    simpa only [DR,n,UF,VG,mul_assoc] using abs_inner_coreDerivative_coreRaising_commutator_le_half hO hD hF a b F G x
  have hRaiseCoeff (b : Fin 3) : |E b*(2*d)| ≤ (2*M*C0)*Rate := by
    have h2d : |2*d| ≤ 2*(C0*r*beta) := by
      rw [abs_mul]
      simpa only [abs_of_pos (by norm_num : (0 : ℝ)<2)] using mul_le_mul_of_nonneg_left hd (by norm_num : (0 : ℝ)≤2)
    rw [abs_mul]
    calc
      _ ≤ M*(2*(C0*r*beta)) := mul_le_mul (hE b) h2d (abs_nonneg _) (by positivity)
      _ = (2*M*C0)*(r*beta) := by ring
      _ ≤ (2*M*C0)*Rate := mul_le_mul_of_nonneg_left hrb (by positivity)
  have hDRCoeff (b a : Fin 3) : |E b*m a| ≤ (M*C0)*Rate := by
    rw [abs_mul]
    calc
      _ ≤ M*(C0*eps*r) := mul_le_mul (hE b) (hm a) (abs_nonneg _) (by positivity)
      _ = (M*C0)*(eps*r) := by ring
      _ ≤ (M*C0)*Rate := mul_le_mul_of_nonneg_left herRate (by positivity)
  have hRaiseTerm (b : Fin 3) : |E b*(2*d)*Rv b| ≤ (4*M*C0)*Rate*n := by
    rw [abs_mul]
    calc
      _ ≤ ((2*M*C0)*Rate)*(2*n) := mul_le_mul (hRaiseCoeff b) (hRaising b) (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hDRTerm (b a : Fin 3) : |E b*m a*DR a b| ≤ (15*M*C0)*Rate*n := by
    rw [abs_mul]
    calc
      _ ≤ ((M*C0)*Rate)*(15*n) := mul_le_mul (hDRCoeff b a) (hDR a b) (abs_nonneg _) (by positivity)
      _ = _ := by ring
  let raise : ℝ := ∑ b : Fin 3, E b*(2*d)*Rv b
  let dr : ℝ := ∑ b : Fin 3, ∑ a : Fin 3, E b*m a*DR a b
  have hraise : |raise| ≤ (12*M*C0)*Rate*n := by
    calc
      _ ≤ ∑ b : Fin 3, |E b*(2*d)*Rv b| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ b : Fin 3, (4*M*C0)*Rate*n := Finset.sum_le_sum (fun b _ => hRaiseTerm b)
      _ = _ := by simp only [Fin.sum_univ_three]; ring
  have hdr : |dr| ≤ (135*M*C0)*Rate*n := by
    calc
      _ ≤ ∑ b : Fin 3, ∑ a : Fin 3, |E b*m a*DR a b| :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun b _ => Finset.abs_sum_le_sum_abs _ _))
      _ ≤ ∑ b : Fin 3, ∑ a : Fin 3, (15*M*C0)*Rate*n :=
        Finset.sum_le_sum (fun b _ => Finset.sum_le_sum (fun a _ => hDRTerm b a))
      _ = _ := by simp only [Fin.sum_univ_three]; ring
  have hexp := congrArg (fun T : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) => ⟪T F x,G x⟫_ℝ)
    (nativeV_referenceFirst_commutator_eq_angular_words hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR l i)
  dsimp only at hexp
  simp only [LinearMap.sub_apply,LinearMap.neg_apply,LinearMap.sum_apply,LinearMap.smul_apply,
    Module.End.mul_apply,nativeReferenceFrameScalar,coreScalar,LinearMap.coe_mk,AddHom.coe_mk,
    Submodule.coe_mk,Submodule.coe_sub,Submodule.coe_neg,Submodule.coe_smul,Submodule.coe_sum,
    Finset.sum_apply,Pi.sub_apply,Pi.neg_apply,Pi.smul_apply,smul_smul,inner_neg_left,inner_sub_left,
    real_inner_smul_left,sum_inner,mul_assoc] at hexp
  have hform : ⟪(ActualModelCommutatorWords.commutator
      (nativeV hO hD hF g1 g2 hg1 L lam δ R p l hg2 hδ hR)
      (nativeReferenceFirstCoefficient hO hD hF g1 hg1 L lam δ R p hδ hR i)) F x,G x⟫_ℝ = -raise-dr := by
    simpa only [raise,dr,E,m,d,Rv,DR,mul_assoc] using hexp
  rw [hform]
  calc
    _ ≤ |raise|+|dr| := by simpa only [sub_eq_add_neg,abs_neg] using abs_add_le (-raise) (-dr)
    _ ≤ (12*M*C0)*Rate*n+(135*M*C0)*Rate*n := add_le_add hraise hdr
    _ = (147*M*C0)*Rate*n := by ring
    _ ≤ C*Rate*n := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hEnlarge hRate) hn
    _ = _ := by dsimp only [Rate,n,UF,VG]; ring

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
