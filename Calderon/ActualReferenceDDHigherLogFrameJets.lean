import Calderon.ActualReferenceDDHigherHCoframeJets
import Calderon.ActualReferenceDDHigherProfileJets

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualReferenceDDHigherLogFrameJets
open ActualReferenceDDHigherHCoframeJets ActualReferenceDDHigherProfileJets
  ActualReferenceDDHigherGeometryJets ActualReferenceDecomposition AmbientReferenceRaising
  SmoothMetricFrame PrincipalCommutator ReferenceDensityBounds ConformalDepth RadiusProfile MetricOperator

lemma referenceFrameDerivative_eq_coordinate_sum
    (g : MatrixField) (L lam : ℝ) (a : Fin 3) (f : R3 → ℝ) :
    referenceFrameDerivative g L lam a f =
      fun x => ∑ j : Fin 3, referenceMetricGramFrame g L (lam,x) a j*
        directionalFDeriv (coordinateDirection j) f x := by
  funext x
  unfold referenceFrameDerivative
  simpa only [smul_eq_mul] using ActualReferenceDecomposition.fderiv_apply_eq_coordinate_sum f x
    (referenceMetricGramFrame g L (lam,x) a)

lemma referenceFrame_directionalFDeriv_eq_coordinate_sum {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : MatrixField) (L lam : ℝ) (a : Fin 3) (f : R3 → E) :
    (fun x => directionalFDeriv (referenceMetricGramFrame g L (lam,x) a) f x) =
      fun x => ∑ j : Fin 3, referenceMetricGramFrame g L (lam,x) a j •
        directionalFDeriv (coordinateDirection j) f x := by
  funext x
  exact ActualReferenceDecomposition.fderiv_apply_eq_coordinate_sum f x
    (referenceMetricGramFrame g L (lam,x) a)

theorem exists_referenceDD_logRadius_frame_uniform_coordinate_word_bounds
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ R : ℝ, 0 < R → ∀ p : ℕ, 1 ≤ p → ∀ x ∈ K,
      let beta := metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L)
        (fun y => Real.log (referenceRadius δ R p L y)) x
      1 ≤ beta → ∀ w : List (Fin 3), w.length ≤ N →
      (∀ a, |coordinateFieldWordPartial w
        (referenceFrameDerivative g L lam a (fun y => Real.log (referenceRadius δ R p L y))) x| ≤
          C*beta^(1+w.length)) ∧
      (∀ a b, |coordinateFieldWordPartial w
        (fun y => directionalFDeriv (referenceMetricGramFrame g L (lam,y) a)
          (referenceFrameDerivative g L lam b (fun v => Real.log (referenceRadius δ R p L v))) y) x| ≤
          C*beta^(2+w.length)) := by
  obtain ⟨M,hM,hgeom⟩ := exists_parameter_coordinate_word_uniform_bound
    (fun t : Fin 3 × Fin 3 => fun z : ℝ × R3 => referenceMetricGramFrame g L z t.1 t.2)
    (fun t => (contDiff_piLp_apply (p := 2) (i := t.2)).comp
      (contDiff_referenceMetricGramFrame g hg L t.1)) K hK (N+1)
  obtain ⟨J,hJ,hlog⟩ := exists_log_referenceRadius_uniform_positive_coordinate_word_bounds
    g hg L hL K hK (N+2)
  let Cgrad : ℝ := 3*(2:ℝ)^(N+1)*M*J
  let Csecond : ℝ := 3*(2:ℝ)^N*M*Cgrad
  let C : ℝ := 1+Cgrad+Csecond
  have hM0 : 0 ≤ M := by linarith
  have hMpos : 0 < M := by linarith
  have hGradPos : 0 < Cgrad := by dsimp [Cgrad]; positivity
  have hSecondPos : 0 < Csecond := by dsimp [Csecond]; positivity
  have hC : 0 < C := by dsimp [C]; linarith
  have hGradC : Cgrad ≤ C := by dsimp [C]; linarith
  have hSecondC : Csecond ≤ C := by dsimp [C]; linarith
  refine ⟨C,hC,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp x hx beta hb w hw
  let f : R3 → ℝ := fun y => Real.log (referenceRadius δ R p L y)
  have hf : ContDiff ℝ ∞ f := contDiff_log_referenceRadius_profile δ R L p hδ hR
  have hb0 : 0 ≤ beta := by linarith
  have hEntryS (a j : Fin 3) : ContDiff ℝ ∞
      (fun y => referenceMetricGramFrame g L (lam,y) a j) :=
    (contDiff_piLp_apply (p := 2) (i := j)).comp
      (contDiff_referenceMetricGramFrame_slice g hg L lam a)
  have hEntry (a j : Fin 3) : HasCoordinateWordJetBound (N+1)
      (fun y => referenceMetricGramFrame g L (lam,y) a j) x M beta 0 := by
    intro v hv
    have ht := hgeom lam hlam x hx (a,j) v hv
    have hm := mul_le_mul_of_nonneg_left (one_le_pow₀ hb : 1 ≤ beta^v.length) hM0
    exact ht.trans (by simpa only [Nat.zero_add,mul_one] using hm)
  have hLogD (j : Fin 3) : HasCoordinateWordJetBound (N+1)
      (directionalFDeriv (coordinateDirection j) f) x J beta 1 := by
    intro v hv
    have ht := hlog lam hlam δ hδ hδ1 R hR p hp x hx (v++[j])
      (by simp only [List.length_append,List.length_singleton]; omega)
      (by simp only [List.length_append,List.length_singleton]; omega)
    simpa only [coordinateFieldWordPartial_append,coordinateFieldWordPartial,
      List.length_append,List.length_singleton,Real.norm_eq_abs,Nat.add_comm,f] using ht
  have hGrad (a : Fin 3) : HasCoordinateWordJetBound (N+1)
      (referenceFrameDerivative g L lam a f) x Cgrad beta 1 := by
    have htermS (j : Fin 3) : ContDiff ℝ ∞
        (fun y => referenceMetricGramFrame g L (lam,y) a j*
          directionalFDeriv (coordinateDirection j) f y) :=
      (hEntryS a j).mul (contDiff_directionalFDeriv (coordinateDirection j) f hf)
    have hterm (j : Fin 3) : HasCoordinateWordJetBound (N+1)
        (fun y => referenceMetricGramFrame g L (lam,y) a j*
          directionalFDeriv (coordinateDirection j) f y) x ((2:ℝ)^(N+1)*M*J) beta 1 :=
      hasCoordinateWordJetBound_mul (N+1)
        (fun y => referenceMetricGramFrame g L (lam,y) a j)
        (directionalFDeriv (coordinateDirection j) f) (hEntryS a j)
        (contDiff_directionalFDeriv (coordinateDirection j) f hf)
        x M J beta 0 1 hM0 hJ.le hb0 (hEntry a j) (hLogD j)
    have ht := hasCoordinateWordJetBound_sum (N+1)
      (fun j : Fin 3 => fun y => referenceMetricGramFrame g L (lam,y) a j*
        directionalFDeriv (coordinateDirection j) f y) htermS x ((2:ℝ)^(N+1)*M*J) beta 1 hterm
    rw [referenceFrameDerivative_eq_coordinate_sum]
    simpa only [Fintype.card_fin,Nat.cast_ofNat,Cgrad,mul_assoc] using ht
  have hSecond (a b : Fin 3) : HasCoordinateWordJetBound N
      (fun y => directionalFDeriv (referenceMetricGramFrame g L (lam,y) a)
        (referenceFrameDerivative g L lam b f) y) x Csecond beta 2 := by
    have hfb : ContDiff ℝ ∞ (referenceFrameDerivative g L lam b f) :=
      contDiff_referenceFrameDerivative g hg L lam b f hf
    have hDfb (j : Fin 3) : HasCoordinateWordJetBound N
        (directionalFDeriv (coordinateDirection j) (referenceFrameDerivative g L lam b f))
        x Cgrad beta 2 :=
      hasCoordinateWordJetBound_coordinate_derivative N
        (referenceFrameDerivative g L lam b f) x Cgrad beta 1 j (hGrad b)
    have htermS (j : Fin 3) : ContDiff ℝ ∞
        (fun y => referenceMetricGramFrame g L (lam,y) a j*
          directionalFDeriv (coordinateDirection j) (referenceFrameDerivative g L lam b f) y) :=
      (hEntryS a j).mul (contDiff_directionalFDeriv (coordinateDirection j) _ hfb)
    have hterm (j : Fin 3) : HasCoordinateWordJetBound N
        (fun y => referenceMetricGramFrame g L (lam,y) a j*
          directionalFDeriv (coordinateDirection j) (referenceFrameDerivative g L lam b f) y)
        x ((2:ℝ)^N*M*Cgrad) beta 2 :=
      hasCoordinateWordJetBound_mul N
        (fun y => referenceMetricGramFrame g L (lam,y) a j)
        (directionalFDeriv (coordinateDirection j) (referenceFrameDerivative g L lam b f))
        (hEntryS a j) (contDiff_directionalFDeriv (coordinateDirection j) _ hfb)
        x M Cgrad beta 0 2 hM0 hGradPos.le hb0
        (hasCoordinateWordJetBound_truncate N (N+1) _ x M beta 0 (hEntry a j) (by omega)) (hDfb j)
    have ht := hasCoordinateWordJetBound_sum N
      (fun j : Fin 3 => fun y => referenceMetricGramFrame g L (lam,y) a j*
        directionalFDeriv (coordinateDirection j) (referenceFrameDerivative g L lam b f) y)
      htermS x ((2:ℝ)^N*M*Cgrad) beta 2 hterm
    rw [referenceFrame_directionalFDeriv_eq_coordinate_sum]
    simpa only [smul_eq_mul,Fintype.card_fin,Nat.cast_ofNat,Csecond,mul_assoc] using ht
  refine ⟨?_,?_⟩
  · intro a
    have ht := hGrad a w (by omega)
    have hm := mul_le_mul_of_nonneg_right hGradC (pow_nonneg hb0 (1+w.length))
    simpa only [Real.norm_eq_abs,f] using ht.trans hm
  · intro a b
    have ht := hSecond a b w hw
    have hm := mul_le_mul_of_nonneg_right hSecondC (pow_nonneg hb0 (2+w.length))
    simpa only [Real.norm_eq_abs,f] using ht.trans hm

end OAI.AnisotropicCalderon.ActualReferenceDDHigherLogFrameJets
