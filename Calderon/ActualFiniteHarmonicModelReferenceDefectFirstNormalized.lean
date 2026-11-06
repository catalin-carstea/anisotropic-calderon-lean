import Calderon.ActualFiniteHarmonicModelDefect
import Calderon.ActualReferenceDDHigherLogFrameJets
import Calderon.ActualReferenceDDHigherCLMProducts

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph
  ActualReferenceDDHigherGeometryJets ActualReferenceDDHigherLogFrameJets
  ActualReferenceDDHigherHCoframeJets
  ActualReferenceDDHigherCLMProducts AmbientReferenceRaising
  ConformalDepth SmoothMetricFrame MovingFrameConnection BoundedAngularShift
  ReferenceWeightedApproximation
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev nativeReferenceDefectFirstNormalizedFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] nativeReferenceDefectFirstNormalizedFunction

def nativeReferenceDefectFirstNormalizedCoefficient
    (hF : SphereFischerInner) (g : MatrixField) (L lam δ R : ℝ) (p : ℕ) :
    R3 → SphereL2 →L[ℝ] SphereL2 :=
  fun x => ∑ a : Fin 3,
    referenceFrameDerivative g L lam a
      (fun y => Real.log (referenceRadius δ R p L y)) x •
      normalizedDerivative hF hO hD a

lemma nativeZField_eq_referenceDefectFirstNormalizedCoefficient
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    nativeZField hO hD hF g hg L lam δ R p F x =
      nativeReferenceDefectFirstNormalizedCoefficient hO hD hF g L lam δ R p x
        (coreWeightOperator hO hD (besselWeight 1) F x) := by
  rw [congrFun (nativeZField_eq_coreAction hO hD hF g hg L lam δ R p hδ hR F) x]
  simp only [coreDefectAction, nativeReferenceDefectFirstNormalizedCoefficient,
    LinearMap.sum_apply, Module.End.mul_apply, coreScalar, coreDerivative,
    coreNormalizedDerivative, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, LinearMap.coe_mk, AddHom.coe_mk,
    Submodule.coe_mk, Submodule.coe_sum, Finset.sum_apply]

theorem exists_nativeReferenceDefectFirstNormalizedCoefficient_uniform_coordinate_word_bounds
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L : ℝ) (hL : 0 < L) (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ R : ℝ, 0 < R → ∀ p : ℕ, 1 ≤ p →
      ∀ x ∈ K, let beta := actualReferenceBeta g L lam δ R p x
      1 ≤ beta → ∀ w : List (Fin 3), w.length ≤ 2 →
      ‖coordinateFieldWordPartial w
        (nativeReferenceDefectFirstNormalizedCoefficient hO hD hF g L lam δ R p) x‖ ≤
          C * beta^(1+w.length) := by
  obtain ⟨J,hJ,hLog⟩ := exists_referenceDD_logRadius_frame_uniform_coordinate_word_bounds
    g hg L hL K hK 2
  let M : ℝ := 1 + ∑ a : Fin 3, ‖normalizedDerivative hF hO hD a‖
  let C : ℝ := 12 * J * M
  have hM : 0 < M := by
    dsimp only [M]
    have ht : 0 ≤ ∑ a : Fin 3, ‖normalizedDerivative hF hO hD a‖ :=
      Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    linarith
  have hC : 0 < C := by dsimp only [C]; positivity
  have hderiv (a : Fin 3) : ‖normalizedDerivative hF hO hD a‖ ≤ M := by
    have ht := Finset.single_le_sum
      (fun b _ => norm_nonneg (normalizedDerivative hF hO hD b))
      (Finset.mem_univ a)
    dsimp only [M]
    linarith
  refine ⟨C,hC,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp x hx beta hb w hw
  have hb0 : 0 ≤ beta := le_trans zero_le_one hb
  let f (a : Fin 3) : R3 → ℝ :=
    referenceFrameDerivative g L lam a (fun y => Real.log (referenceRadius δ R p L y))
  have hfS (a : Fin 3) : ContDiff ℝ ∞ (f a) :=
    contDiff_referenceFrameDerivative g hg L lam a _
      (contDiff_log_referenceRadius_profile δ R L p hδ hR)
  have hfJ (a : Fin 3) : HasCoordinateWordJetBound 2 (f a) x J beta 1 := by
    intro v hv
    simpa only [Real.norm_eq_abs, f, beta, actualReferenceBeta] using
      (hLog lam hlam δ hδ hδ1 R hR p hp x hx hb v hv).1 a
  have hconstJ (a : Fin 3) : HasCoordinateWordJetBound 2
      (fun _ : R3 => normalizedDerivative hF hO hD a) x M beta 0 :=
    hasCoordinateWordJetBound_const_normed 2 _ x M beta (hderiv a) hb0
  have hterm (a : Fin 3) : HasCoordinateWordJetBound 2
      (fun y => f a y • normalizedDerivative hF hO hD a) x
      (4 * J * M) beta 1 := by
    have ht := hasCoordinateWordJetBound_smul 2 (f a)
      (fun _ : R3 => normalizedDerivative hF hO hD a)
      (hfS a) contDiff_const x J M beta 1 0 hJ.le hM.le hb0
      (hfJ a) (hconstJ a)
    convert ht using 1 <;> norm_num
  have hsum := hasCoordinateWordJetBound_sum 2
    (fun a y => f a y • normalizedDerivative hF hO hD a)
    (fun a => (hfS a).smul contDiff_const) x (4 * J * M) beta 1 hterm
  have hsum' : HasCoordinateWordJetBound 2
      (nativeReferenceDefectFirstNormalizedCoefficient hO hD hF g L lam δ R p)
      x C beta 1 := by
    convert hsum using 1 <;>
      first | rfl | (simp only [Fintype.card_fin, Nat.cast_ofNat, C] <;> ring)
  simpa only [Nat.add_comm] using hsum' w hw

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
