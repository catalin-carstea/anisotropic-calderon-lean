import Calderon.ActualReferenceZeroEProfileCaps
import Calderon.ReferenceFrameUniformComparison
import Calderon.ActualHigherSCoordinateWeightBounds

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Metric
open scoped BigOperators ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualReferenceAngularCoefficientJets
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualRetainedGeneratorMultiplierGains ActualReferenceZeroECommutators ReferenceFrameUniformComparison
  ReferenceDensityBounds ConformalDepth SmoothMetricFrame MovingFrameConnection ReferenceWeightedApproximation

private lemma compact_family_cap {X V I : Type*} [TopologicalSpace X]
    [SeminormedAddCommGroup V] [Fintype I] (K : Set X) (hK : IsCompact K)
    (f : I → X → V) (hf : ∀ i, ContinuousOn (f i) K) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ i : I, ∀ x ∈ K, ‖f i x‖ ≤ M := by
  classical
  choose C hC using fun i : I => hK.exists_bound_of_continuousOn (hf i)
  have hs0 : 0 ≤ ∑ i : I, |C i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  refine ⟨1+∑ i : I, |C i|,by linarith,?_⟩
  intro i x hx
  apply (hC i x hx).trans
  calc
    C i ≤ |C i| := le_abs_self _
    _ ≤ ∑ j : I, |C j| := Finset.single_le_sum (fun j _ => abs_nonneg (C j)) (Finset.mem_univ i)
    _ ≤ 1+∑ j : I, |C j| := by linarith

private lemma norm_fderiv_slice_le {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : ℝ × R3 → V) (hf : ContDiff ℝ ∞ f) (q : ℝ) (x : R3) (M : ℝ)
    (hM : 0 ≤ M) (hcap : ‖fderiv ℝ f (q,x)‖ ≤ M) :
    ‖fderiv ℝ (fun y : R3 => f (q,y)) x‖ ≤ M := by
  have ht : HasFDerivAt (fun y : R3 => (q,y)) (ContinuousLinearMap.inr ℝ ℝ R3) x :=
    (hasFDerivAt_const q x).prodMk (hasFDerivAt_id x)
  have hd := ((hf.differentiable (by simp) (q,x)).hasFDerivAt.comp x ht).fderiv
  refine ContinuousLinearMap.opNorm_le_bound _ hM (fun v => ?_)
  have hdu : fderiv ℝ (fun y : R3 => f (q,y)) x v = fderiv ℝ f (q,x) (0,v) :=
    congrArg (fun A : R3 →L[ℝ] V => A v) hd
  rw [hdu]
  calc
    _ ≤ ‖fderiv ℝ f (q,x)‖*‖((0,v) : ℝ × R3)‖ := (fderiv ℝ f (q,x)).le_opNorm _
    _ = ‖fderiv ℝ f (q,x)‖*‖v‖ := by
      simp only [Prod.norm_def,norm_zero,max_eq_right (norm_nonneg v)]
    _ ≤ M*‖v‖ := mul_le_mul_of_nonneg_right hcap (norm_nonneg v)

private lemma norm_fderiv_apply_le {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (c : E → F →L[ℝ] G) (u : E → F) (x : E)
    (hc : DifferentiableAt ℝ c x) (hu : DifferentiableAt ℝ u x) :
    ‖fderiv ℝ (fun y => c y (u y)) x‖ ≤
      ‖c x‖*‖fderiv ℝ u x‖+‖fderiv ℝ c x‖*‖u x‖ := by
  rw [fderiv_clm_apply hc hu]
  calc
    _ ≤ ‖(c x).comp (fderiv ℝ u x)‖+‖(fderiv ℝ c x).flip (u x)‖ := norm_add_le _ _
    _ ≤ ‖c x‖*‖fderiv ℝ u x‖+‖(fderiv ℝ c x).flip‖*‖u x‖ :=
      add_le_add (ContinuousLinearMap.opNorm_comp_le _ _) (((fderiv ℝ c x).flip).le_opNorm _)
    _ = _ := by rw [ContinuousLinearMap.opNorm_flip]

private inductive GeometryIndex where
  | frame (i : Fin 3) | frameDerivative (i : Fin 3)
  | connection (i a b : Fin 3) | connectionDerivative (i a b : Fin 3)
  deriving Fintype, DecidableEq

private def geometryQuantity (g : MatrixField) (L : ℝ) : GeometryIndex → (ℝ × R3) → ℝ
  | .frame i, z => ‖referenceMetricGramFrame g L z i‖
  | .frameDerivative i, z => ‖fderiv ℝ (fun t : ℝ × R3 => referenceMetricGramFrame g L t i) z‖
  | .connection i a b, z => |referenceGramConnectionCoefficient g L i a b z|
  | .connectionDerivative i a b, z => ‖fderiv ℝ (referenceGramConnectionCoefficient g L i a b) z‖

private lemma continuous_geometryQuantity (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L : ℝ) (idx : GeometryIndex) : Continuous (geometryQuantity g L idx) := by
  cases idx with
  | frame i => exact (contDiff_referenceMetricGramFrame g hg L i).continuous.norm
  | frameDerivative i =>
    exact ((contDiff_referenceMetricGramFrame g hg L i).fderiv_right (m := ∞) (by simp)).continuous.norm
  | connection i a b => exact (contDiff_referenceGramConnectionCoefficient g hg L i a b).continuous.abs
  | connectionDerivative i a b =>
    exact ((contDiff_referenceGramConnectionCoefficient g hg L i a b).fderiv_right
      (m := ∞) (by simp)).continuous.norm

private theorem exists_geometry_first_caps (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L : ℝ) (K : Set R3) (hK : IsCompact K) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ q ∈ Icc (0 : ℝ) 1, ∀ x ∈ K, ∀ i : Fin 3,
      ‖referenceMetricGramFrame g L (q,x) i‖ ≤ M ∧
      ‖fderiv ℝ (fun y : R3 => referenceMetricGramFrame g L (q,y) i) x‖ ≤ M ∧
      ∀ a b : Fin 3, |referenceGramConnectionCoefficient g L i a b (q,x)| ≤ M ∧
        ‖fderiv ℝ (fun y : R3 => referenceGramConnectionCoefficient g L i a b (q,y)) x‖ ≤ M := by
  obtain ⟨M,hM,hcap⟩ := compact_family_cap (Icc (0 : ℝ) 1 ×ˢ K) (isCompact_Icc.prod hK)
    (geometryQuantity g L) (fun idx => (continuous_geometryQuantity g hg L idx).continuousOn)
  have hc (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (x : R3) (hx : x ∈ K) (idx : GeometryIndex) :
      geometryQuantity g L idx (q,x) ≤ M :=
    (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hcap idx (q,x) ⟨hq,hx⟩)
  refine ⟨M,hM,?_⟩
  intro q hq x hx i
  refine ⟨hc q hq x hx (.frame i),?_,?_⟩
  · exact norm_fderiv_slice_le _ (contDiff_referenceMetricGramFrame g hg L i)
      q x M (zero_le_one.trans hM) (hc q hq x hx (.frameDerivative i))
  · intro a b
    exact ⟨hc q hq x hx (.connection i a b),
      norm_fderiv_slice_le _ (contDiff_referenceGramConnectionCoefficient g hg L i a b)
        q x M (zero_le_one.trans hM) (hc q hq x hx (.connectionDerivative i a b))⟩

/-- Every original angular coefficient is globally smooth, including its actual log-radius part. -/
theorem contDiff_reference_angular_coefficient (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L q dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (i : Fin 3) (V : Generator) :
    ContDiff ℝ ∞ (fun y => referenceAngularZeroCoefficient g L q dr Ar p y i V) := by
  cases V with
  | inl ab =>
    change ContDiff ℝ ∞ (fun y : R3 => (1/2 : ℝ)*referenceGramConnectionCoefficient g L i ab.1 ab.2 (q,y))
    exact contDiff_const.mul ((contDiff_referenceGramConnectionCoefficient g hg L i ab.1 ab.2).comp
      (contDiff_const.prodMk contDiff_id))
  | inr z =>
    have hR := ActualScalarPrincipalAdjoint.contDiff_referenceRadius_actual dr Ar p L hdr hAr
    have hLog : ContDiff ℝ ∞ (fun y => Real.log (referenceRadius dr Ar p L y)) :=
      hR.log (fun y => (referenceRadius_pos dr Ar p L y hdr hAr).ne')
    change ContDiff ℝ ∞ (fun y => (fderiv ℝ (fun z => Real.log (referenceRadius dr Ar p L z)) y)
      (referenceMetricGramFrame g L (q,y) i))
    exact (hLog.fderiv_right (m := ∞) (by simp)).clm_apply
      ((contDiff_referenceMetricGramFrame g hg L i).comp (contDiff_const.prodMk contDiff_id))

attribute [local irreducible] referenceMetricGramFrame referenceRadius

/-- Actual value and first-physical-derivative caps, selected before every original profile. -/
theorem exists_reference_angular_coefficient_first_caps (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L : ℝ) (hL : 0 < L) (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ q ∈ Icc (0 : ℝ) 1, ∀ dr : ℝ, 0 < dr → dr ≤ 1 →
      ∀ Ar : ℝ, 0 < Ar → ∀ p : ℕ, 1 ≤ p → ∀ x ∈ K,
      1 ≤ actualReferenceBeta g L q dr Ar p x → ∀ i : Fin 3, ∀ V : Generator,
      |referenceAngularZeroCoefficient g L q dr Ar p x i V| ≤ C*actualReferenceBeta g L q dr Ar p x ∧
      ‖fderiv ℝ (fun y => referenceAngularZeroCoefficient g L q dr Ar p y i V) x‖ ≤
        C*(actualReferenceBeta g L q dr Ar p x)^2 := by
  obtain ⟨M,hM,hGeom⟩ := exists_geometry_first_caps g hg L K hK
  obtain ⟨J0,hJ0one,hJet⟩ := exists_dilated_referenceRadius_fixed_uniform_jet_envelope
    g hg L hL K hK 2
  let J : ℝ := J0^2
  have hJ : 1 ≤ J := one_le_pow₀ hJ0one
  have hJ0le : J0 ≤ J := by dsimp only [J]; nlinarith only [hJ0one]
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hJ0 : 0 ≤ J := zero_le_one.trans hJ
  have hMJ : 0 ≤ M*J := mul_nonneg hM0 hJ0
  let C : ℝ := 1+M+2*M*J
  have hC : 0 < C := by dsimp only [C]; nlinarith only [hM0,hMJ]
  have hMC : M ≤ C := by dsimp only [C]; nlinarith only [hMJ]
  have hMJC : M*J ≤ C := by dsimp only [C]; nlinarith only [hM0,hMJ]
  have h2MJC : 2*M*J ≤ C := by dsimp only [C]; linarith only [hM0]
  refine ⟨C,hC,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp x hx hb i V
  let beta := actualReferenceBeta g L q dr Ar p x
  have hb0 : 0 ≤ beta := zero_le_one.trans hb
  have hb12 : beta ≤ beta^2 := by nlinarith only [hb]
  have hb2 : 1 ≤ beta^2 := hb.trans hb12
  have hMscale : M ≤ C*beta := hMC.trans
    (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hb hC.le)
  have hMscale2 : M ≤ C*beta^2 := hMC.trans
    (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hb2 hC.le)
  cases V with
  | inl ab =>
    have hg0 := ((hGeom q hq x hx i).2.2 ab.1 ab.2).1
    have hg1 := ((hGeom q hq x hx i).2.2 ab.1 ab.2).2
    have hdc : DifferentiableAt ℝ
        (fun y : R3 => referenceGramConnectionCoefficient g L i ab.1 ab.2 (q,y)) x :=
      (((contDiff_referenceGramConnectionCoefficient g hg L i ab.1 ab.2).comp
        (contDiff_const.prodMk contDiff_id)).differentiable (by simp) x)
    constructor
    · change |(1/2 : ℝ)*referenceGramConnectionCoefficient g L i ab.1 ab.2 (q,x)| ≤ C*beta
      rw [abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<1/2)]
      exact (mul_le_mul_of_nonneg_left hg0 (by norm_num)).trans
        ((by linarith only [hM0] : (1/2 : ℝ)*M ≤ M).trans hMscale)
    · change ‖fderiv ℝ (fun y : R3 => (1/2 : ℝ)*referenceGramConnectionCoefficient g L i ab.1 ab.2 (q,y)) x‖ ≤ C*beta^2
      rw [fderiv_const_mul hdc,norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0 : ℝ)<1/2)]
      exact (mul_le_mul_of_nonneg_left hg1 (by norm_num)).trans
        ((by linarith only [hM0] : (1/2 : ℝ)*M ≤ M).trans hMscale2)
  | inr z =>
    let ell : R3 → R3 →L[ℝ] ℝ := fun y => fderiv ℝ
      (fun z => Real.log (referenceRadius dr Ar p L z)) y
    let X : R3 → R3 := fun y => referenceMetricGramFrame g L (q,y) i
    have hR := ActualScalarPrincipalAdjoint.contDiff_referenceRadius_actual dr Ar p L hdr hAr
    have hLog : ContDiff ℝ ∞ (fun y => Real.log (referenceRadius dr Ar p L y)) :=
      hR.log (fun y => (referenceRadius_pos dr Ar p L y hdr hAr).ne')
    have hell : ContDiff ℝ ∞ ell := hLog.fderiv_right (m := ∞) (by simp)
    have hX : ContDiff ℝ ∞ X :=
      (contDiff_referenceMetricGramFrame g hg L i).comp (contDiff_const.prodMk contDiff_id)
    have he0 : ‖ell x‖ ≤ J*beta := by
      have h1 : ‖ell x‖ ≤ J0*beta := by
        simpa only [ell,beta,norm_iteratedFDeriv_one,pow_one,actualReferenceBeta]
          using hJet q hq dr hdr hdr1 Ar hAr p hp x hx 1 (by omega) (by omega)
      exact h1.trans (mul_le_mul_of_nonneg_right hJ0le hb0)
    have he1 : ‖fderiv ℝ ell x‖ ≤ J*beta^2 := by
      rw [← norm_iteratedFDeriv_one,norm_iteratedFDeriv_fderiv]
      simpa only [ell,beta,actualReferenceBeta,mul_pow,J]
        using hJet q hq dr hdr hdr1 Ar hAr p hp x hx 2 (by omega) (by omega)
    have hx0 : ‖X x‖ ≤ M := (hGeom q hq x hx i).1
    have hx1 : ‖fderiv ℝ X x‖ ≤ M := (hGeom q hq x hx i).2.1
    constructor
    · change |ell x (X x)| ≤ C*beta
      rw [← Real.norm_eq_abs]
      calc
        _ ≤ ‖ell x‖*‖X x‖ := (ell x).le_opNorm _
        _ ≤ (J*beta)*M := mul_le_mul he0 hx0 (norm_nonneg _) (mul_nonneg hJ0 hb0)
        _ = (M*J)*beta := by ring
        _ ≤ C*beta := mul_le_mul_of_nonneg_right hMJC hb0
    · change ‖fderiv ℝ (fun y => ell y (X y)) x‖ ≤ C*beta^2
      calc
        _ ≤ ‖ell x‖*‖fderiv ℝ X x‖+‖fderiv ℝ ell x‖*‖X x‖ :=
          norm_fderiv_apply_le ell X x (hell.differentiable (by simp) x) (hX.differentiable (by simp) x)
        _ ≤ (J*beta)*M+(J*beta^2)*M := add_le_add
          (mul_le_mul he0 hx1 (norm_nonneg _) (mul_nonneg hJ0 hb0))
          (mul_le_mul he1 hx0 (norm_nonneg _) (mul_nonneg hJ0 (sq_nonneg beta)))
        _ = (M*J)*beta+(M*J)*beta^2 := by ring
        _ ≤ (M*J)*beta^2+(M*J)*beta^2 :=
          add_le_add (mul_le_mul_of_nonneg_left hb12 hMJ) le_rfl
        _ = (2*M*J)*beta^2 := by ring
        _ ≤ C*beta^2 := mul_le_mul_of_nonneg_right h2MJC (sq_nonneg beta)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualReferenceAngularCoefficientJets

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualReferenceAngularCoefficientJets.contDiff_reference_angular_coefficient
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualReferenceAngularCoefficientJets.exists_reference_angular_coefficient_first_caps
