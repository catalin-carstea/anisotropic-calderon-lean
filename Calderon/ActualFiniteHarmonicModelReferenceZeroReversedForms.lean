import Calderon.ActualFiniteHarmonicModelReferenceZeroFactorJets
import Calderon.ActualFiniteHarmonicModelReversedAngularShiftForms
import Calderon.ActualFiniteHarmonicModelReferenceZeroOperatorJets

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph BoundedAngularShift
  ActualReferenceDDHigherGeometryJets ActualReferenceDDHigherHCoframeJets ActualReferenceDDHigherCLMProducts
  ActualReferenceParallelRaising ActualReferenceDDSpectralTransport AmbientReferenceRaising
  SmoothMetricFrame MovingFrameConnection ReferenceDensityBounds ReferenceWeightedApproximation
  PrincipalCommutator ConformalDepth ActualModelCommutatorWords
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev referenceZeroReversedFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] referenceZeroReversedFunction


lemma coordinateFieldWordPartial_referenceZeroDefect_inner_input_factors
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R)
    (w : List (Fin 3)) (F G : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    let LF : Fin 3 → R3 → SphereL2 →L[ℝ] SphereL2 := fun a y =>
      -(normalizedReferenceAngularConnection hO hD g L lam y (referenceMetricGramFrame g L (lam,y) a)) +
        referenceFrameDerivative g L lam a (fun z => Real.log (referenceRadius δ R p L z)) y •
          (ContinuousLinearMap.id ℝ SphereL2 - (2 : ℝ) • inverseDegreeMultiplier hO hD)
    let RF : Fin 3 → R3 → SphereL2 →L[ℝ] SphereL2 := fun a y =>
      normalizedReferenceAngularConnection hO hD g L lam y (referenceMetricGramFrame g L (lam,y) a) +
        referenceFrameDerivative g L lam a (fun z => Real.log (referenceRadius δ R p L z)) y •
          (ContinuousLinearMap.id ℝ SphereL2 - inverseDegreeMultiplier hO hD)
    ⟪coordinateFieldWordPartial w
      (nativeReferenceZeroDefectAngularCoefficient hO hD hF g hg L lam δ R p) x
      (coreWeightOperator hO hD (besselWeight 2) F x),G x⟫_ℝ =
      2 * ∑ a : Fin 3,
        (⟪normalizedDerivative hF hO hD a
          (coordinateFieldWordPartial w (LF a) x (coreWeightOperator hO hD (besselWeight 2) F x)),G x⟫_ℝ -
        ⟪normalizedRaising hF hO hD a
          (coordinateFieldWordPartial w (RF a) x (coreWeightOperator hO hD (besselWeight 2) F x)),G x⟫_ℝ) := by
  intro LF RF
  let HN := nativeReferenceZeroDefectAngularCoefficient hO hD hF g hg L lam δ R p
  let u2 := coreWeightOperator hO hD (besselWeight 2) F x
  let v := G x
  let J : (SphereL2 →L[ℝ] SphereL2) →L[ℝ] ℝ :=
    (innerSL ℝ v).comp (ContinuousLinearMap.apply ℝ SphereL2 u2)
  let JD (a : Fin 3) : (SphereL2 →L[ℝ] SphereL2) →L[ℝ] ℝ :=
    (innerSL ℝ v).comp ((normalizedDerivative hF hO hD a).comp
      (ContinuousLinearMap.apply ℝ SphereL2 u2))
  let JR (a : Fin 3) : (SphereL2 →L[ℝ] SphereL2) →L[ℝ] ℝ :=
    (innerSL ℝ v).comp ((normalizedRaising hF hO hD a).comp
      (ContinuousLinearMap.apply ℝ SphereL2 u2))
  have hJ (A : SphereL2 →L[ℝ] SphereL2) : J A = ⟪A u2,v⟫_ℝ := by
    change ⟪v,A u2⟫_ℝ = _
    exact real_inner_comm _ _
  have hJD (a : Fin 3) (A : SphereL2 →L[ℝ] SphereL2) :
      JD a A = ⟪normalizedDerivative hF hO hD a (A u2),v⟫_ℝ := by
    change ⟪v,normalizedDerivative hF hO hD a (A u2)⟫_ℝ = _
    exact real_inner_comm _ _
  have hJR (a : Fin 3) (A : SphereL2 →L[ℝ] SphereL2) :
      JR a A = ⟪normalizedRaising hF hO hD a (A u2),v⟫_ℝ := by
    change ⟪v,normalizedRaising hF hO hD a (A u2)⟫_ℝ = _
    exact real_inner_comm _ _
  have hA (a : Fin 3) := ActualReferenceModelTrace.contDiff_normalizedReferenceAngularConnection_frame hO hD g hg L lam a
  have hf (a : Fin 3) := contDiff_referenceFrameDerivative g hg L lam a _
    (contDiff_log_referenceRadius_profile δ R L p hδ hR)
  have hLF (a : Fin 3) : ContDiff ℝ ∞ (LF a) :=
    (hA a).neg.add ((hf a).smul contDiff_const)
  have hRF (a : Fin 3) : ContDiff ℝ ∞ (RF a) :=
    (hA a).add ((hf a).smul contDiff_const)
  have hHN : ContDiff ℝ ∞ HN :=
    contDiff_nativeReferenceZeroDefectAngularCoefficient hO hD hF g hg L lam δ R p hδ hR
  let T (a : Fin 3) : R3 → ℝ := fun y => JD a (LF a y)-JR a (RF a y)
  let S : R3 → ℝ := fun y => ∑ a : Fin 3, T a y
  have hT (a : Fin 3) : ContDiff ℝ ∞ (T a) :=
    ((JD a).contDiff.comp (hLF a)).sub ((JR a).contDiff.comp (hRF a))
  have hS : ContDiff ℝ ∞ S := ContDiff.sum (fun a _ => hT a)
  have hfunc : (fun y => J (HN y)) = fun y => 2*S y := by
    funext y
    change J ((2 : ℝ) • ∑ a : Fin 3,
      ((normalizedDerivative hF hO hD a).comp (LF a y)-
        (normalizedRaising hF hO hD a).comp (RF a y))) = _
    simp only [map_smul,map_sum,map_sub,smul_eq_mul]
    rfl
  have hfixed (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
      (A : R3 → E) (hA : ContDiff ℝ ∞ A) (Q : E →L[ℝ] ℝ) :
      coordinateFieldWordPartial w (fun y => Q (A y)) =
        fun y => Q (coordinateFieldWordPartial w A y) := by
    induction w with
    | nil => rfl
    | cons k w ih =>
      change directionalFDeriv (coordinateDirection k)
        (coordinateFieldWordPartial w (fun y => Q (A y))) =
          fun y => Q (directionalFDeriv (coordinateDirection k) (coordinateFieldWordPartial w A) y)
      rw [ih]
      funext y
      exact ActualReferenceDecomposition.directionalFDeriv_fixed_map Q
        (coordinateFieldWordPartial w A) (contDiff_coordinateFieldWordPartial w A hA)
        (coordinateDirection k) y
  have htwo : coordinateFieldWordPartial w (fun y => 2*S y) =
      fun y => 2*coordinateFieldWordPartial w S y :=
    hfixed ℝ S hS ((2 : ℝ) • ContinuousLinearMap.id ℝ ℝ)
  have hTerm (a : Fin 3) : coordinateFieldWordPartial w (T a) =
      fun y => JD a (coordinateFieldWordPartial w (LF a) y)-
        JR a (coordinateFieldWordPartial w (RF a) y) := by
    change coordinateFieldWordPartial w (fun y => JD a (LF a y)+ -(JR a (RF a y))) = _
    rw [coordinateFieldWordPartial_add w (fun y => JD a (LF a y))
      (fun y => -(JR a (RF a y))) ((JD a).contDiff.comp (hLF a))
      (((JR a).contDiff.comp (hRF a)).neg),
      coordinateFieldWordPartial_neg w (fun y => JR a (RF a y)) ((JR a).contDiff.comp (hRF a)),
      hfixed _ (LF a) (hLF a) (JD a),hfixed _ (RF a) (hRF a) (JR a)]
    rfl
  have hsum : coordinateFieldWordPartial w S =
      fun y => ∑ a : Fin 3, coordinateFieldWordPartial w (T a) y :=
    coordinateFieldWordPartial_sum w T hT
  have hw := congrArg (fun f : R3 → ℝ => coordinateFieldWordPartial w f) hfunc
  rw [hfixed _ HN hHN J,htwo,hsum] at hw
  simp_rw [hTerm] at hw
  have he := congrFun hw x
  rw [hJ] at he
  simp_rw [hJD,hJR] at he
  exact he

theorem exists_referenceZeroDefect_uniform_half_threehalf_forms
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L : ℝ) (hL : 0 < L) (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, ∀ hδ : 0 < δ, δ ≤ 1 → ∀ R : ℝ, ∀ hR : 0 < R,
      ∀ p : ℕ, 1 ≤ p → ∀ x ∈ K, let beta := actualReferenceBeta g L lam δ R p x
      1 ≤ beta → ∀ w : List (Fin 3), w.length ≤ 2 →
      ∀ F G : smoothCompactFiniteSphereCore hO hD,
      |⟪coordinateFieldWordPartial w
        (nativeReferenceZeroDefectAngularCoefficient hO hD hF g hg L lam δ R p) x
        (coreWeightOperator hO hD (besselWeight 2) F x), G x⟫_ℝ| ≤
          (C * beta^(1+w.length)) *
            ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖ *
            ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) G x‖ := by
  obtain ⟨CJ,hCJ,hFactors⟩ := exists_referenceZeroDefect_input_factors_uniform_coordinate_word_bounds
    hO hD g hg L hL K hK
  let KD : ℝ := 2*(2 : ℝ)^(1/2 : ℝ)
  let KR : ℝ := 2
  let C : ℝ := 1+6*(KD+KR)*CJ
  have hKD : 0 ≤ KD := by dsimp only [KD]; positivity
  have hKR : 0 ≤ KR := by norm_num [KR]
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C,hC,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp x hx beta hb w hw F G
  let LF : Fin 3 → R3 → SphereL2 →L[ℝ] SphereL2 := fun a y =>
    -(normalizedReferenceAngularConnection hO hD g L lam y (referenceMetricGramFrame g L (lam,y) a)) +
      referenceFrameDerivative g L lam a (fun z => Real.log (referenceRadius δ R p L z)) y •
        (ContinuousLinearMap.id ℝ SphereL2 - (2 : ℝ) • inverseDegreeMultiplier hO hD)
  let RF : Fin 3 → R3 → SphereL2 →L[ℝ] SphereL2 := fun a y =>
    normalizedReferenceAngularConnection hO hD g L lam y (referenceMetricGramFrame g L (lam,y) a) +
      referenceFrameDerivative g L lam a (fun z => Real.log (referenceRadius δ R p L z)) y •
        (ContinuousLinearMap.id ℝ SphereL2 - inverseDegreeMultiplier hO hD)
  let u2 := coreWeightOperator hO hD (besselWeight 2) F x
  let nf := ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖
  let ng := ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) G x‖
  let b : ℝ := beta^(1+w.length)
  have hb0 : 0 ≤ b := pow_nonneg (le_trans zero_le_one hb) _
  have hFactor (a : Fin 3) :
      ‖coordinateFieldWordPartial w (LF a) x‖ ≤ CJ*b ∧
      ‖coordinateFieldWordPartial w (RF a) x‖ ≤ CJ*b ∧
      PreservesSphereSpectralGraphs hO hD (coordinateFieldWordPartial w (LF a) x) ∧
      PreservesSphereSpectralGraphs hO hD (coordinateFieldWordPartial w (RF a) x) :=
    hFactors lam hlam δ hδ hδ1 R hR p hp x hx hb a w hw
  have hd (a : Fin 3) :
      |⟪normalizedDerivative hF hO hD a (coordinateFieldWordPartial w (LF a) x u2),G x⟫_ℝ| ≤
        KD*CJ*b*nf*ng := by
    have ht := abs_inner_normalizedDerivative_weight_two_le_half_threehalf hO hD hF a
      (coordinateFieldWordPartial w (LF a) x) (hFactor a).2.2.1 F G x
    exact ht.trans (by
      change (KD*‖coordinateFieldWordPartial w (LF a) x‖)*nf*ng ≤ _
      have hn := mul_le_mul_of_nonneg_left (hFactor a).1 hKD
      have hn2 := mul_le_mul_of_nonneg_right hn (norm_nonneg _ : 0 ≤ nf)
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hn2 (norm_nonneg _ : 0 ≤ ng))
  have hr (a : Fin 3) :
      |⟪normalizedRaising hF hO hD a (coordinateFieldWordPartial w (RF a) x u2),G x⟫_ℝ| ≤
        KR*CJ*b*nf*ng := by
    have ht := abs_inner_normalizedRaising_weight_two_le_half_threehalf hO hD hF a
      (coordinateFieldWordPartial w (RF a) x) (hFactor a).2.2.2 F G x
    exact ht.trans (by
      change (KR*‖coordinateFieldWordPartial w (RF a) x‖)*nf*ng ≤ _
      have hn := mul_le_mul_of_nonneg_left (hFactor a).2.1 hKR
      have hn2 := mul_le_mul_of_nonneg_right hn (norm_nonneg _ : 0 ≤ nf)
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hn2 (norm_nonneg _ : 0 ≤ ng))
  rw [coordinateFieldWordPartial_referenceZeroDefect_inner_input_factors hO hD hF g hg
    L lam δ R p hδ hR w F G x]
  change |2*∑ a : Fin 3,
    (⟪normalizedDerivative hF hO hD a (coordinateFieldWordPartial w (LF a) x u2),G x⟫_ℝ -
    ⟪normalizedRaising hF hO hD a (coordinateFieldWordPartial w (RF a) x u2),G x⟫_ℝ)| ≤ (C*b)*nf*ng
  rw [abs_mul,show |(2 : ℝ)|=2 by norm_num]
  calc
    _ ≤ 2*∑ a : Fin 3,
      |⟪normalizedDerivative hF hO hD a (coordinateFieldWordPartial w (LF a) x u2),G x⟫_ℝ -
      ⟪normalizedRaising hF hO hD a (coordinateFieldWordPartial w (RF a) x u2),G x⟫_ℝ| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by norm_num)
    _ ≤ 2*∑ a : Fin 3, (KD+KR)*CJ*b*nf*ng := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum
      intro a _
      have htri :
          |⟪normalizedDerivative hF hO hD a (coordinateFieldWordPartial w (LF a) x u2),G x⟫_ℝ -
          ⟪normalizedRaising hF hO hD a (coordinateFieldWordPartial w (RF a) x u2),G x⟫_ℝ| ≤
          |⟪normalizedDerivative hF hO hD a (coordinateFieldWordPartial w (LF a) x u2),G x⟫_ℝ| +
          |⟪normalizedRaising hF hO hD a (coordinateFieldWordPartial w (RF a) x u2),G x⟫_ℝ| := by
        simpa only [sub_eq_add_neg,abs_neg] using abs_add_le
          (⟪normalizedDerivative hF hO hD a (coordinateFieldWordPartial w (LF a) x u2),G x⟫_ℝ)
          (-⟪normalizedRaising hF hO hD a (coordinateFieldWordPartial w (RF a) x u2),G x⟫_ℝ)
      exact htri.trans (by nlinarith [hd a,hr a])
    _ = (6*(KD+KR)*CJ*b)*nf*ng := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      ring
    _ ≤ (C*b)*nf*ng := by
      have hc : 6*(KD+KR)*CJ ≤ C := by dsimp only [C]; linarith
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hb0) (norm_nonneg _))
        (norm_nonneg _)

theorem exists_nativeReferenceZeroDefect_uniform_half_threehalf_forms
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L : ℝ) (hL : 0 < L) (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, ∀ hδ : 0 < δ, δ ≤ 1 → ∀ R : ℝ, ∀ hR : 0 < R,
      ∀ p : ℕ, 1 ≤ p → ∀ x ∈ K, let beta := actualReferenceBeta g L lam δ R p x
      1 ≤ beta →
      let N := 2 * (nativeReferenceAdjointZeroCoefficient hO hD hF g hg L lam δ R p hδ hR -
        nativeReferenceZeroCoefficient hO hD hF g hg L lam δ R p hδ hR)
      ∀ i k : Fin 3, ∀ F G : smoothCompactFiniteSphereCore hO hD,
      |⟪N F x, G x⟫_ℝ| ≤ (C * beta) *
        ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖ *
        ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) G x‖ ∧
      |⟪coefficientDerivative (coreDirectionalDerivative hO hD (coordinateDirection i)) N F x, G x⟫_ℝ| ≤
        (C * beta^2) * ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖ *
        ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) G x‖ ∧
      |⟪coefficientDerivative (coreDirectionalDerivative hO hD (coordinateDirection i))
        (coefficientDerivative (coreDirectionalDerivative hO hD (coordinateDirection k)) N) F x, G x⟫_ℝ| ≤
        (C * beta^3) * ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖ *
        ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) G x‖ := by
  obtain ⟨C,hC,hBounds⟩ := exists_referenceZeroDefect_uniform_half_threehalf_forms
    hO hD hF g hg L hL K hK
  refine ⟨C,hC,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp x hx beta hb N i k F G
  have h0 := hBounds lam hlam δ hδ hδ1 R hR p hp x hx hb [] (by norm_num) F G
  have h1 := hBounds lam hlam δ hδ hδ1 R hR p hp x hx hb [i] (by norm_num) F G
  have h2 := hBounds lam hlam δ hδ hδ1 R hR p hp x hx hb [i,k] (by norm_num) F G
  dsimp only [N]
  refine ⟨?_,?_,?_⟩
  · rw [nativeReferenceZeroDefect_secondAngularCoefficient_apply hO hD hF g hg L lam δ R p hδ hR F x]
    simpa only [coordinateFieldWordPartial,List.length_nil,Nat.add_zero,pow_one] using h0
  · rw [coefficientDerivative_nativeReferenceZeroDefect_secondAngular_apply hO hD hF g hg L lam δ R p hδ hR]
    simpa only [coordinateFieldWordPartial,List.length_cons,List.length_nil] using h1
  · rw [coefficientDerivative_second_nativeReferenceZeroDefect_secondAngular_apply hO hD hF g hg L lam δ R p hδ hR]
    simpa only [coordinateFieldWordPartial,List.length_cons,List.length_nil] using h2

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
