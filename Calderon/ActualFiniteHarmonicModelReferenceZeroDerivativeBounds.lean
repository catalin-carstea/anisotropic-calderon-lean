import Calderon.ActualFiniteHarmonicModelReferenceZeroDerivativeExpansion
import Calderon.ActualFiniteHarmonicModelQuadraticThreehalfForms
import Calderon.ActualFiniteHarmonicModelReferenceExpansionCoefficientBounds

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph
  ActualModelCommutatorWords SmoothMetricFrame MovingFrameConnection PrincipalCommutator
  ReferenceDensityBounds ReferenceWeightedApproximation ActualHorizontalNormBridge
  ActualReferenceDDHigherGeometryJets ActualReferenceDDHigherLogFrameJets
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev referenceZeroDerivativeBoundsFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) := ⟨fun F => F.val⟩
attribute [local instance] referenceZeroDerivativeBoundsFunction

theorem exists_nativeReferenceZeroDerivativeExpansionMass_uniform_bound
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ R : ℝ, 0 < R → ∀ p : ℕ, 1 ≤ p → ∀ x ∈ K,
      1 ≤ actualReferenceBeta g L lam δ R p x → ∀ j : Fin 3,
      nativeReferenceZeroDerivativeExpansionMass g L lam δ R p (coordinateDirection j) x ≤
        C*(actualReferenceBeta g L lam δ R p x)^2 := by
  obtain ⟨M,hM,hgeom⟩ := exists_parameter_coordinate_word_uniform_bound
    (fun t : Fin 3 × Fin 3 × Fin 3 => fun z : ℝ × R3 =>
      referenceFrameConnectionJoint g L (fun q : ℝ × R3 => referenceMetricGramFrame g L q t.1) z t.2.1 t.2.2)
    (fun t => contDiff_referenceFrameConnectionJoint g hg L
      (fun q : ℝ × R3 => referenceMetricGramFrame g L q t.1)
      (contDiff_referenceMetricGramFrame g hg L t.1) t.2.1 t.2.2) K hK 1
  obtain ⟨J,hJ,hprof⟩ := exists_referenceDD_logRadius_frame_uniform_coordinate_word_bounds g hg L hL K hK 1
  refine ⟨3*((9/2:ℝ)*M+J),by have hm : 0 < M := lt_of_lt_of_le zero_lt_one hM; positivity,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp x hx hb j
  let beta := actualReferenceBeta g L lam δ R p x
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  have hMscale : M ≤ M*beta^2 := le_mul_of_one_le_right hM0 (one_le_pow₀ hb)
  have hgcoef (a b c : Fin 3) : |directionalFDeriv (coordinateDirection j)
      (fun y => referenceFrameConnectionCoefficient g L lam y (referenceMetricGramFrame g L (lam,y) a) b c) x| ≤ M*beta^2 := by
    have ht := hgeom lam hlam x hx (a,b,c) [j] (by simp)
    have he : (fun y => referenceFrameConnectionJoint g L
        (fun q : ℝ × R3 => referenceMetricGramFrame g L q a) (lam,y) b c) =
        (fun y => referenceFrameConnectionCoefficient g L lam y (referenceMetricGramFrame g L (lam,y) a) b c) := by
      funext y
      exact referenceFrameConnectionJoint_eq g hg L _ (lam,y) b c
    rw [he] at ht
    have ht' : |directionalFDeriv (coordinateDirection j)
        (fun y => referenceFrameConnectionCoefficient g L lam y (referenceMetricGramFrame g L (lam,y) a) b c) x| ≤ M := by
      simpa only [coordinateFieldWordPartial,Real.norm_eq_abs] using ht
    exact ht'.trans hMscale
  have hq (a : Fin 3) : |directionalFDeriv (coordinateDirection j)
      (AmbientReferenceRaising.referenceFrameDerivative g L lam a (fun y => Real.log (ConformalDepth.referenceRadius δ R p L y))) x| ≤ J*beta^2 := by
    simpa only [coordinateFieldWordPartial,List.length_cons,List.length_nil,Nat.reduceAdd,beta,actualReferenceBeta] using
      (hprof lam hlam δ hδ hδ1 R hR p hp x hx hb [j] (by simp)).1 a
  have hpair (a : Fin 3) : (1/2:ℝ)*(∑ b : Fin 3, ∑ c : Fin 3,
      |directionalFDeriv (coordinateDirection j)
        (fun y => referenceFrameConnectionCoefficient g L lam y (referenceMetricGramFrame g L (lam,y) a) b c) x|)+
      |directionalFDeriv (coordinateDirection j)
        (AmbientReferenceRaising.referenceFrameDerivative g L lam a (fun y => Real.log (ConformalDepth.referenceRadius δ R p L y))) x| ≤
        (((9/2:ℝ)*M)+J)*beta^2 := by
    have hs := Finset.sum_le_sum (fun b (_ : b ∈ (Finset.univ : Finset (Fin 3))) =>
      Finset.sum_le_sum (fun c (_ : c ∈ (Finset.univ : Finset (Fin 3))) => hgcoef a b c))
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] at hs
    calc
      _ ≤ (1/2:ℝ)*(3*(3*(M*beta^2)))+J*beta^2 := add_le_add
        (mul_le_mul_of_nonneg_left hs (by norm_num)) (hq a)
      _ = _ := by ring
  unfold nativeReferenceZeroDerivativeExpansionMass
  calc
    _ ≤ ∑ a : Fin 3, (((9/2:ℝ)*M)+J)*beta^2 := Finset.sum_le_sum (fun a _ => hpair a)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat]; ring

theorem exists_nativeReferenceZero_derivative_uniform_quadratic_expansion
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L : ℝ) (hL : 0 < L) (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, ∀ hδ : 0 < δ, δ ≤ 1 → ∀ R : ℝ, ∀ hR : 0 < R,
      ∀ p : ℕ, 1 ≤ p → ∀ x ∈ K, 1 ≤ actualReferenceBeta g L lam δ R p x → ∀ j : Fin 3,
      HasCoreScalarExpansionBound hO hD
        (fun ij : CoreAngularGeneratorIndex × CoreAngularGeneratorIndex => coreAngularGenerator hO hD hF ij.1*coreAngularGenerator hO hD hF ij.2)
        (coefficientDerivative (coreDirectionalDerivative hO hD (coordinateDirection j))
          (nativeReferenceZeroCoefficient hO hD hF g hg L lam δ R p hδ hR)) x
        (C*(actualReferenceBeta g L lam δ R p x)^2) := by
  obtain ⟨C,hC,hbound⟩ := exists_nativeReferenceZeroDerivativeExpansionMass_uniform_bound g hg L hL K hK
  refine ⟨C,hC,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp x hx hb j
  exact hasCoreScalarExpansionBound_mono hO hD _ _ x _ _
    (hasCoreScalarExpansionBound_nativeReferenceZero_derivative hO hD hF g hg L lam δ R p hδ hR (coordinateDirection j) x)
    (hbound lam hlam δ hδ hδ1 R hR p hp x hx hb j)

theorem exists_nativeReferenceZero_derivative_uniform_threehalf_half_forms
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L : ℝ) (hL : 0 < L) (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, ∀ hδ : 0 < δ, δ ≤ 1 → ∀ R : ℝ, ∀ hR : 0 < R,
      ∀ p : ℕ, 1 ≤ p → ∀ x ∈ K, 1 ≤ actualReferenceBeta g L lam δ R p x → ∀ j : Fin 3,
      ∀ U V : smoothCompactFiniteSphereCore hO hD,
      |⟪coefficientDerivative (coreDirectionalDerivative hO hD (coordinateDirection j))
          (nativeReferenceZeroCoefficient hO hD hF g hg L lam δ R p hδ hR) U x,V x⟫_ℝ| ≤
        (C*(actualReferenceBeta g L lam δ R p x)^2)*
          ‖coreWeightOperator hO hD (besselWeight (3/2:ℝ)) U x‖ *
          ‖coreWeightOperator hO hD (besselWeight (1/2:ℝ)) V x‖ := by
  obtain ⟨C,hC,hExp⟩ := exists_nativeReferenceZero_derivative_uniform_quadratic_expansion hO hD hF g hg L hL K hK
  have hM : 0 < coreAngularGeneratorBound hO hD := by have ht := (coreAngularGeneratorBound_bounds hO hD).1; linarith
  refine ⟨C*(coreAngularGeneratorBound hO hD)^2,by positivity,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp x hx hb j U V
  have ht := coreAngularExpansion_quadratic_threehalf_half_form_bound hO hD hF _ x
    (C*(actualReferenceBeta g L lam δ R p x)^2) (hExp lam hlam δ hδ hδ1 R hR p hp x hx hb j) U V
  convert ht using 1 <;> ring

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
