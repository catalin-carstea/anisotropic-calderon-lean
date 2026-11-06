import Calderon.ProfileHessianEnergy

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory MvPolynomial
open scoped ContDiff InnerProductSpace Gradient Topology
namespace OAI.AnisotropicCalderon.IntegratedProfileConvexity
open RadiusProfile ConformalDepth MetricOperator AngularPolynomial SphereHarmonic
  WeightedFischerSquare SmoothMetricFrame FischerConnectionTransport
  IntegratedFischerIdentities FiniteRaisingEnergy WeightedRaisingBounds
  ProfileHessianEnergy ReferenceDensityBounds
attribute [local irreducible] referenceMetricGramFrame referenceConnectionFamily
  metricOperatorField referenceMetric dilatedMetric finitePolynomialField
variable {ι : Type*} [Fintype ι]

def referenceProfileWeightedFrameEnergy (g : MatrixField) (lam δ R L : ℝ) (p : ℕ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (k s : ℝ) : ℝ :=
  ∫ x : R3, referenceDensityFamily g L (lam,x)*(referenceProfileNorm g lam δ R p L x)⁻¹*
    referenceWeightedFrameEnergy g L lam b c (referenceLogRadius δ R p L) k s x

def referenceProfileWeightedTraceSquare (g : MatrixField) (lam δ R L : ℝ) (p : ℕ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (k s : ℝ) : ℝ :=
  ∫ x : R3, referenceDensityFamily g L (lam,x)*(referenceProfileNorm g lam δ R p L x)⁻¹*fischerInner
    (referenceLoweredWeightedTraceField g L lam b c (referenceLogRadius δ R p L) k s x)
    (referenceLoweredWeightedTraceField g L lam b c (referenceLogRadius δ R p L) k s x)

lemma referenceProfileWeightedFrameEnergy_nonneg (g : MatrixField) (hg : IsAdmissibleMetric g)
    (lam δ R L : ℝ) (p : ℕ) (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (k s : ℝ) :
    0 ≤ referenceProfileWeightedFrameEnergy g lam δ R L p b c k s := by
  apply integral_nonneg
  intro x
  exact mul_nonneg (mul_nonneg (referenceDensityFamily_pos g hg L (lam,x)).le
    (inv_nonneg.mpr (Real.sqrt_nonneg _))) (Finset.sum_nonneg (fun i _ => fischerInner_self_nonneg _))

lemma referenceProfileWeightedTraceSquare_nonneg (g : MatrixField) (hg : IsAdmissibleMetric g)
    (lam δ R L : ℝ) (p : ℕ) (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (k s : ℝ) :
    0 ≤ referenceProfileWeightedTraceSquare g lam δ R L p b c k s := by
  apply integral_nonneg
  intro x
  exact mul_nonneg (mul_nonneg (referenceDensityFamily_pos g hg L (lam,x)).le
    (inv_nonneg.mpr (Real.sqrt_nonneg _))) (fischerInner_self_nonneg _)

lemma referenceProfileTrace_convex_bound_global (g : MatrixField) (hg : IsAdmissibleMetric g)
    (K : Set R3) (hK : IsClosed K) (L lam δ R : ℝ) (hL : 0 < L) (hδ : 0 < δ) (hR : 0 < R)
    (p k : ℕ) (hp : 1 ≤ p) (hk : 1 ≤ k)
    (b : ι → MvPolynomial (Fin 3) ℝ) (hb : ∀ a, b a ∈ harmonicHomogeneous k)
    (c : R3 → ι → ℝ) (hc : ContDiff ℝ ∞ c) (hzero : ∀ x ∉ K, finitePolynomialField b c x = 0)
    (a : ℝ) (ha : 0 ≤ a) (hbeta : ∀ x ∈ K, a ≤ referenceProfileNorm g lam δ R p L x) (x : R3) :
    fischerInner (referenceLoweredWeightedTraceField g L lam b c (referenceLogRadius δ R p L) k 1 x)
      (referenceLoweredWeightedTraceField g L lam b c (referenceLogRadius δ R p L) k 1 x) ≤
      ((k:ℝ)+2)*referenceWeightedFrameEnergy g L lam b c (referenceLogRadius δ R p L) k 1 x -
      a*((k:ℝ)+2)*(referenceProfileNorm g lam δ R p L x)⁻¹*
        referenceWeightedFrameEnergy g L lam b c (referenceLogRadius δ R p L) k 1 x +
      2*a*(referenceProfileNorm g lam δ R p L x)⁻¹*fischerInner
        (referenceLoweredWeightedTraceField g L lam b c (referenceLogRadius δ R p L) k (-1) x)
        (referenceLoweredWeightedTraceField g L lam b c (referenceLogRadius δ R p L) k (-1) x) +
      8*a*(k:ℝ)^3*referenceProfileNorm g lam δ R p L x*
        fischerInner (finitePolynomialField b c x) (finitePolynomialField b c x) := by
  by_cases hx : x ∈ K
  · have hbpos := referenceProfileNorm_pos g hg lam δ R L p hδ hR hL hp x
    have h := referenceProfileTrace_convex_bound g hg L lam δ R p k hk b hb c x a ha hbpos (hbeta x hx)
    convert h using 1
    field_simp [hbpos.ne']
    <;> ring
  · simp only [referenceLoweredWeightedTraceField_eq_zero_off_closed g hg L lam b c hc K hK hzero x hx,
      referenceWeightedFrameEnergy_eq_zero_off_closed g hg L lam b c hc K hK hzero x hx,
      hzero x hx,fischerInner_zero_left,mul_zero,zero_sub,zero_add,neg_zero,add_zero,le_refl]

lemma referenceProfileTrace_convex_integrated_bound (g : MatrixField) (hg : IsAdmissibleMetric g)
    (K : Set R3) (hK : IsClosed K) (L lam δ R : ℝ) (hL : 0 < L) (hδ : 0 < δ) (hR : 0 < R)
    (p k : ℕ) (hp : 1 ≤ p) (hk : 1 ≤ k)
    (b : ι → MvPolynomial (Fin 3) ℝ) (hb : ∀ a, b a ∈ harmonicHomogeneous k)
    (c : R3 → ι → ℝ) (hc : ContDiff ℝ ∞ c) (hcompact : HasCompactSupport c)
    (hzero : ∀ x ∉ K, finitePolynomialField b c x = 0)
    (a : ℝ) (ha : 0 ≤ a) (hbeta : ∀ x ∈ K, a ≤ referenceProfileNorm g lam δ R p L x) :
    referenceLoweredWeightedTraceSquare g L lam b c (referenceLogRadius δ R p L) k 1 ≤
      ((k:ℝ)+2)*(∫ x : R3, referenceDensityFamily g L (lam,x)*referenceWeightedFrameEnergy g L lam b c (referenceLogRadius δ R p L) k 1 x) -
      a*((k:ℝ)+2)*referenceProfileWeightedFrameEnergy g lam δ R L p b c k 1 +
      2*a*referenceProfileWeightedTraceSquare g lam δ R L p b c k (-1) +
      8*a*(k:ℝ)^3*referenceProfileMass g lam δ R L p b c := by
  let X : R3 → ℝ := fun x => referenceDensityFamily g L (lam,x)*referenceWeightedFrameEnergy g L lam b c (referenceLogRadius δ R p L) k 1 x
  let Y : R3 → ℝ := fun x => referenceDensityFamily g L (lam,x)*(referenceProfileNorm g lam δ R p L x)⁻¹*referenceWeightedFrameEnergy g L lam b c (referenceLogRadius δ R p L) k 1 x
  let Z : R3 → ℝ := fun x => referenceDensityFamily g L (lam,x)*(referenceProfileNorm g lam δ R p L x)⁻¹*fischerInner
    (referenceLoweredWeightedTraceField g L lam b c (referenceLogRadius δ R p L) k (-1) x)
    (referenceLoweredWeightedTraceField g L lam b c (referenceLogRadius δ R p L) k (-1) x)
  let M : R3 → ℝ := fun x => referenceDensityFamily g L (lam,x)*referenceProfileNorm g lam δ R p L x*fischerInner (finitePolynomialField b c x) (finitePolynomialField b c x)
  have hr : ContDiff ℝ ∞ (fun x : R3 => referenceDensityFamily g L (lam,x)) :=
    (contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id)
  have hf := contDiff_log_referenceRadius δ R p L hδ hR
  have hX : Integrable X := integrable_referenceWeightedFrameEnergy g hg L lam _ hr.continuous b c _ k 1 hc hf hcompact
  have hY : Integrable Y := integrable_referenceProfileNorm_inv_frameEnergy g hg lam δ R L p hδ hR hL hp b c k 1 hc hcompact
  have hZ : Integrable Z := integrable_referenceProfileNorm_inv_traceSquare g hg lam δ R L p hδ hR hL hp b c k (-1) hc hcompact
  have hM : Integrable M := integrable_referenceProfileNorm_fischerSquare g hg lam δ R L p hδ hR b c hc hcompact
  have hS := integrable_referenceLoweredWeightedTrace_square g hg L lam b c _ k 1 hc hf hcompact
  let A : R3 → ℝ := fun x => ((k:ℝ)+2)*X x
  let B : R3 → ℝ := fun x => a*((k:ℝ)+2)*Y x
  let Cc : R3 → ℝ := fun x => 2*a*Z x
  let Dd : R3 → ℝ := fun x => 8*a*(k:ℝ)^3*M x
  have hA : Integrable A := hX.const_mul _
  have hB : Integrable B := hY.const_mul _
  have hCc : Integrable Cc := hZ.const_mul _
  have hDd : Integrable Dd := hM.const_mul _
  calc
    _ ≤ ∫ x : R3, ((A-B)+Cc) x+Dd x := by
      apply integral_mono hS (((hA.sub hB).add hCc).add hDd)
      intro x
      have hh := mul_le_mul_of_nonneg_left
        (referenceProfileTrace_convex_bound_global g hg K hK L lam δ R hL hδ hR p k hp hk b hb c hc hzero a ha hbeta x)
        (referenceDensityFamily_pos g hg L (lam,x)).le
      change referenceDensityFamily g L (lam,x)*_ ≤ _
      apply hh.trans_eq
      dsimp only [A,B,Cc,Dd,X,Y,Z,M,Pi.add_apply,Pi.sub_apply]
      ring
    _ = _ := by
      rw [integral_add ((hA.sub hB).add hCc) hDd]
      change (∫ x : R3, (A-B) x+Cc x)+(∫ x : R3, Dd x) = _
      rw [integral_add (hA.sub hB) hCc]
      change (∫ x : R3, A x-B x)+(∫ x : R3, Cc x)+(∫ x : R3, Dd x) = _
      rw [integral_sub hA hB]
      simp only [A,B,Cc,Dd,integral_const_mul]
      rfl

lemma referenceProfileWeightedTraceSquare_le (g : MatrixField) (hg : IsAdmissibleMetric g)
    (K : Set R3) (hK : IsClosed K) (L lam δ R : ℝ) (hL : 0 < L) (hδ : 0 < δ) (hR : 0 < R)
    (p : ℕ) (hp : 1 ≤ p) (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ)
    (hc : ContDiff ℝ ∞ c) (hcompact : HasCompactSupport c)
    (hzero : ∀ x ∉ K, finitePolynomialField b c x = 0)
    (beta0 : ℝ) (hb0 : 0 < beta0) (hbeta : ∀ x ∈ K, beta0 ≤ referenceProfileNorm g lam δ R p L x)
    (k s : ℝ) : referenceProfileWeightedTraceSquare g lam δ R L p b c k s ≤
      beta0⁻¹*referenceLoweredWeightedTraceSquare g L lam b c (referenceLogRadius δ R p L) k s := by
  have hZ := integrable_referenceProfileNorm_inv_traceSquare g hg lam δ R L p hδ hR hL hp b c k s hc hcompact
  have hS := integrable_referenceLoweredWeightedTrace_square g hg L lam b c _ k s hc
    (contDiff_log_referenceRadius δ R p L hδ hR) hcompact
  calc
    _ ≤ ∫ x : R3, beta0⁻¹*(referenceDensityFamily g L (lam,x)*fischerInner
        (referenceLoweredWeightedTraceField g L lam b c (referenceLogRadius δ R p L) k s x)
        (referenceLoweredWeightedTraceField g L lam b c (referenceLogRadius δ R p L) k s x)) := by
      apply integral_mono hZ (hS.const_mul _)
      intro x
      by_cases hx : x ∈ K
      · have hi : (referenceProfileNorm g lam δ R p L x)⁻¹ ≤ beta0⁻¹ := by
          simpa only [one_div] using one_div_le_one_div_of_le hb0 (hbeta x hx)
        have hm := mul_le_mul_of_nonneg_right hi (mul_nonneg
          (referenceDensityFamily_pos g hg L (lam,x)).le (fischerInner_self_nonneg
            (referenceLoweredWeightedTraceField g L lam b c (referenceLogRadius δ R p L) k s x)))
        calc
          _ = (referenceProfileNorm g lam δ R p L x)⁻¹*(referenceDensityFamily g L (lam,x)*fischerInner
              (referenceLoweredWeightedTraceField g L lam b c (referenceLogRadius δ R p L) k s x)
              (referenceLoweredWeightedTraceField g L lam b c (referenceLogRadius δ R p L) k s x)) := by ring
          _ ≤ _ := hm
      · simp only [referenceLoweredWeightedTraceField_eq_zero_off_closed g hg L lam b c hc K hK hzero x hx,
          fischerInner_zero_left,mul_zero,le_refl]
    _ = _ := integral_const_mul _ _

lemma referenceProfileTrace_convex_uniform_integrated_bound (g : MatrixField) (hg : IsAdmissibleMetric g)
    (K : Set R3) (hK : IsClosed K) (L lam δ R : ℝ) (hL : 0 < L) (hδ : 0 < δ) (hR : 0 < R)
    (p k : ℕ) (hp : 1 ≤ p) (hk : 1 ≤ k)
    (b : ι → MvPolynomial (Fin 3) ℝ) (hb : ∀ a, b a ∈ harmonicHomogeneous k)
    (c : R3 → ι → ℝ) (hc : ContDiff ℝ ∞ c) (hcompact : HasCompactSupport c)
    (hzero : ∀ x ∉ K, finitePolynomialField b c x = 0)
    (a beta0 : ℝ) (ha : 0 ≤ a) (hb0 : 0 < beta0) (hab : a ≤ beta0)
    (hbeta : ∀ x ∈ K, beta0 ≤ referenceProfileNorm g lam δ R p L x) :
    referenceLoweredWeightedTraceSquare g L lam b c (referenceLogRadius δ R p L) k 1 ≤
      ((k:ℝ)+2)*(∫ x : R3, referenceDensityFamily g L (lam,x)*referenceWeightedFrameEnergy g L lam b c (referenceLogRadius δ R p L) k 1 x) -
      a*((k:ℝ)+2)*referenceProfileWeightedFrameEnergy g lam δ R L p b c k 1 +
      (2*a/beta0)*referenceLoweredWeightedTraceSquare g L lam b c (referenceLogRadius δ R p L) k (-1) +
      8*a*(k:ℝ)^3*referenceProfileMass g lam δ R L p b c := by
  have h1 := referenceProfileTrace_convex_integrated_bound g hg K hK L lam δ R hL hδ hR p k hp hk b hb c hc hcompact hzero a ha
    (fun x hx => hab.trans (hbeta x hx))
  have h2 := mul_le_mul_of_nonneg_left
    (referenceProfileWeightedTraceSquare_le g hg K hK L lam δ R hL hδ hR p hp b c hc hcompact hzero beta0 hb0 hbeta k (-1))
    (show 0 ≤ 2*a by positivity)
  have h2' : 2*a*referenceProfileWeightedTraceSquare g lam δ R L p b c k (-1) ≤
      (2*a/beta0)*referenceLoweredWeightedTraceSquare g L lam b c (referenceLogRadius δ R p L) k (-1) := by
    simpa only [div_eq_mul_inv,mul_assoc] using h2
  linarith

end OAI.AnisotropicCalderon.IntegratedProfileConvexity
