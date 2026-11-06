import Calderon.ActualTZeroGenuineReverse
import Calderon.ActualSecondGeometryCaps
import Calderon.ProfileRadiusJets
import Calderon.ReferenceWeightedApproximation

/-!
Before-code: ../T-zero-correction-uniform-before-source-nov03-night-v001/UPFRONT.md.
Actual original scalar/atom caps for the full raw N-1 correction.
This is not the literal L00 energy estimate or Main's coercivity.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Filter Metric
open scoped BigOperators ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTZeroCorrectionUniform
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFullEGainedAssembly ActualFiniteHarmonicCore
  ActualAllAngularAtomGainedRoom ActualTZeroGenuineReverse ActualReferenceZeroECommutators
  ActualSecondGeometryCaps ActualHigherSFormation ReferenceDensityBounds ActualRetainedGeneratorMultiplierGains
  AmbientReferenceRaising ConformalDepth ReferenceWeightedApproximation SmoothMetricFrame
  MovingFrameConnection

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete
@[instance_reducible] private def highHalfNormed : NormedAddCommGroup (Hi →L[ℝ] Half) := inferInstance
@[instance_reducible] private def highHalfSpace : NormedSpace ℝ (Hi →L[ℝ] Half) := inferInstance
attribute [local instance] highHalfNormed highHalfSpace

variable (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3))
  (ε C ρ : ℝ) (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace)
  (Room : ReferenceGaugeNormalReciprocalRoom g L Φ a
    (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ)))
  (hreg : FixedDirichletRegularity)
  (data : FullEPhysicalEndpointRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg)
local notation "ARoom" d:max => AllAngularAtomRoom
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data d
local notation "Corr" => referenceZeroAdjointCorrection
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data
local notation "Tq" => higherSParam L
local notation "ParamRoom" d:max => Set.prod (commonRoom y0 ρ d) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "cc" => referenceAngularZeroCoefficient g L
local notation "fi" q:max dr:max Ar:max p:max x:max i:max =>
  referenceFrameDerivative g L q i (fun y => Real.log (referenceRadius dr Ar p L y)) x

attribute [local irreducible] loweringHigh angularAtomHigh angularAtomLow
  angularAtomReverseHigh angularAtomReverseLow referenceZeroAdjointCorrection

/-- The actual fixed-room correction cap precedes every later profile and input. -/
theorem exists_original_correction_uniform_beta_bound
    (hL : 0 < L) {d : ℝ} (P : ARoom d) (K : Set R3) (hK : IsCompact K) :
    ∃ CT : ℝ, 0 < CT ∧ ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ dr : ℝ, 0 < dr → dr ≤ 1 → ∀ Ar : ℝ, 0 < Ar →
      ∀ p : ℕ, 1 ≤ p → ∀ x ∈ K,
      (Tq dr Ar p q) x ∈ ParamRoom d →
      1 ≤ actualReferenceBeta g L q dr Ar p x →
      ‖Corr P q dr Ar p x‖ ≤ CT*actualReferenceBeta g L q dr Ar p x := by
  obtain ⟨MA,hMA,hAtoms,hGains⟩ := P.finiteCaps 0
  obtain ⟨MG,hMG,hGeom⟩ := exists_geometryCaps g g hg hg L K hK
  obtain ⟨J,hJ,hJet⟩ := exists_dilated_referenceRadius_fixed_uniform_jet_envelope
    g hg L hL K hK 1
  have hMA0 : 0 ≤ MA := zero_le_one.trans hMA
  have hMG0 : 0 ≤ MG := zero_le_one.trans hMG
  have hJ0 : 0 ≤ J := zero_le_one.trans hJ
  let S : ℝ := MG*(J+1)
  have hS : 0 < S := by dsimp only [S]; positivity
  have hMGS : MG ≤ S := by dsimp only [S]; nlinarith only [hMG0,hJ0]
  let CT : ℝ := 33*S*MA
  have hCT : 0 < CT := by dsimp only [CT]; positivity
  refine ⟨CT,hCT,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp x hx ht hb
  let beta : ℝ := actualReferenceBeta g L q dr Ar p x
  let ell : R3 →L[ℝ] ℝ := fderiv ℝ (fun y => Real.log (referenceRadius dr Ar p L y)) x
  have hb0 : 0 ≤ beta := zero_le_one.trans hb
  have hEll : ‖ell‖ ≤ J*beta := by
    simpa only [ell,beta,norm_iteratedFDeriv_one,pow_one,actualReferenceBeta]
      using hJet q hq dr hdr hdr1 Ar hAr p hp x hx 1 (by norm_num) (by norm_num)
  have hf0 (i : Fin 3) : |fi q dr Ar p x i| ≤ MG*J*beta := by
    rw [← Real.norm_eq_abs]
    change ‖ell (referenceMetricGramFrame g L (q,x) i)‖ ≤ MG*J*beta
    calc
      _ ≤ ‖ell‖*‖referenceMetricGramFrame g L (q,x) i‖ := ell.le_opNorm _
      _ ≤ (J*beta)*MG := mul_le_mul hEll ((hGeom q hq x hx).frame i)
        (norm_nonneg _) (mul_nonneg hJ0 hb0)
      _ = _ := by ring
  have hf (i : Fin 3) : |fi q dr Ar p x i| ≤ S*beta :=
    (hf0 i).trans (mul_le_mul_of_nonneg_right (by dsimp only [S]; nlinarith only [hMG0]) hb0)
  have hMGb : MG ≤ S*beta := hMGS.trans (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hb hS.le)
  have hc (i : Fin 3) (V : Generator) : |cc q dr Ar p x i V| ≤ S*beta := by
    cases V with
    | inl ab =>
      have he := (hGeom q hq x hx).connection i ab.2 ab.1
      simp only [referenceAngularZeroCoefficient,abs_mul,abs_div,abs_one,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at ⊢
      calc
        _ ≤ (1/2 : ℝ)*MG := mul_le_mul_of_nonneg_left he (by norm_num)
        _ ≤ MG := by linarith only [hMG0]
        _ ≤ S*beta := hMGb
    | inr z => exact hf i
  have hG (i : Fin 3) (V : Generator) :
      ‖P.gainHigh (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inl V)) ((Tq dr Ar p q) x)‖ ≤ MA := by
    simpa only [norm_iteratedFDerivWithin_zero] using
      (hGains (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inl V)) 0 le_rfl _ ht).1
  have ha (i : Fin 3) : ‖loweringHigh hF hO hD i‖ ≤ MA := by
    simpa only [norm_iteratedFDerivWithin_zero,angularAtomReverseHigh] using
      (hAtoms (Sum.inr (Sum.inr i)) 0 le_rfl _ ht).2.2.1
  have h := norm_referenceZeroAdjointCorrection_le
    hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data
    P q dr Ar p x S MA beta hS.le hMA0 hb0 hc hf hG ha
  simpa only [CT,beta] using h

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTZeroCorrectionUniform
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTZeroCorrectionUniform.exists_original_correction_uniform_beta_bound
