import Calderon.ActualTSFirstQuadraticBilinearCaps
import Calderon.ActualTSSymmetricFirstGreen
import Calderon.ActualTSFirstLinearZeroIntegral

/-! Actual per-word symmetric Green bound; full D10 matching and gains remain. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Filter Metric
open scoped BigOperators ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSFirstQuadraticActualGreen
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFullEGainedAssembly ActualAllAngularAtomGainedRoom
  ActualFiniteHarmonicCore ConformalDepth ReferenceDensityBounds ReferenceWeightedApproximation
  ActualTSTripleBilinearCoefficient

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "PL" => ActualHigherSScalarCommutatorNativeForm.halfDualPairingL
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete
local notation "Coeff" => ActualTSActualTripleRoomCaps.TripleCoefficientSpace
attribute [local instance] ActualTSActualTripleRoomCaps.tripleCoefficientNormedGroup
  ActualTSActualTripleRoomCaps.tripleCoefficientNormedSpace
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


open MeasureTheory PrincipalCommutator ActualTSFirstQuadraticBilinearCaps
  ActualTSPrincipalLowerReferenceOrders ActualTSSymmetricFirstGreen
  ActualHigherSZeroScalarNativeForm ActualHigherSScalarCommutatorForm
  ReferenceWeightedApproximation ReferenceDensityBounds ActualHigherSQuadraticZeroWords
  ActualScalarPrincipalAdjoint ActualScalarPrincipalSelfFormBound
  ActualHigherSScalarCommutatorNativeForm

@[instance_reducible] private def highDualNormed :
    NormedAddCommGroup (Hi →L[ℝ] ℝ) := inferInstance
@[instance_reducible] private def highDualSpace :
    NormedSpace ℝ (Hi →L[ℝ] ℝ) := inferInstance
attribute [local instance] highDualNormed highDualSpace

/-- Original continuous-dual evaluation, with no Hilbert-space identification. -/
def highEvaluationPairing : Hi →L[ℝ] (Hi →L[ℝ] ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.apply ℝ ℝ

theorem highEvaluationPairing_apply (v : Hi) (phi : Hi →L[ℝ] ℝ) :
    highEvaluationPairing v phi=phi v := rfl

local notation "EP" => highEvaluationPairing
local notation "UF" => ActualHigherSFormation.higherSInput hO hD
local notation "WCoeff" => weightedTripleCoefficient
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0

/-- Exact symmetric first density for each original weighted triple coefficient. -/
def actualWeightedSymmetricDensity (g2 : MatrixField) (q dr Ar : ℝ) (p : ℕ)
    (F : smoothCompactFiniteSphereCore hO hD) (i l : Fin 3) (z : ZeroWord)
    (aa bb cc : AngularAtom) : R3 → ℝ :=
  symmetricFirstDensity (E := Hi) (F := Hi →L[ℝ] ℝ) EP (fun x => referenceDensityFamily g L (q,x)) (UF F)
    (WCoeff g2 q dr Ar p i l z aa bb cc) (coordinateDirection l)
local notation "SD" => actualWeightedSymmetricDensity
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0

/-- Actual original coefficients close all symmetric-Green premises internally.
The positive constant and room precede every later profile and finite word index. -/
theorem exists_actual_uniform_weighted_triple_symmetric_integral_bound
    (hL : 0 < L) {d : ℝ} (hd : 0 < d) (P : ARoom d)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) :
    ∃ Cgreen etaRoom : ℝ, 0 < Cgreen ∧ 0 < etaRoom ∧ etaRoom ≤ 1 ∧
      ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, ∀ hAr : 0 < Ar,
      ∀ p : ℕ, 1 ≤ p → ∀ eta : ℝ, 0 ≤ eta → eta ≤ etaRoom →
      ∀ K : Set R3, IsCompact K → K ⊆ ball y0 ρ →
      ∀ F : smoothCompactFiniteSphereCore hO hD, tsupport F.val ⊆ K →
      (∀ x ∈ K, 1 ≤ actualReferenceBeta g L q dr Ar p x) →
      (∀ x ∈ K, referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) →
      ∀ i l : Fin 3, ∀ z : ZeroWord, ∀ aa bb cc : AngularAtom,
      Integrable (SD g2 q dr Ar p F i l z aa bb cc) ∧
        |∫ x, SD g2 q dr Ar p F i l z aa bb cc x| ≤
          Cgreen*eta*∫ x, referenceDensityFamily g L (q,x)*
            actualReferenceBeta g L q dr Ar p x*‖UF F x‖^2 := by
  obtain ⟨Cweight,hCweight,etaRoom,heRoom,heRoom1,hCaps⟩ :=
    exists_actual_uniform_weighted_triple_first_caps
      hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data hL hd P g2 hg2
  obtain ⟨M,hM,hMuCaps⟩ := exists_density_coordinate_relative_bound g hg L
    (closedBall y0 ρ) (isCompact_closedBall _ _)
  let Bgreen : ℝ := ‖EP‖*Cweight*(M+1)
  have hBgreen : 0 ≤ Bgreen := by dsimp only [Bgreen]; positivity
  refine ⟨Bgreen+1,etaRoom,by positivity,heRoom,heRoom1,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta he K hK hKball F hsupp hb hs i l z aa bb cc
  let U : R3 → Hi := UF F
  let beta := actualReferenceBeta g L q dr Ar p
  let mu : R3 → ℝ := fun x => referenceDensityFamily g L (q,x)
  let A : R3 → Coeff := WCoeff g2 q dr Ar p i l z aa bb cc
  have hm : ContDiff ℝ ∞ mu :=
    (contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id)
  have hmu (x : R3) : 0 ≤ mu x := (referenceDensityFamily_pos g hg L (q,x)).le
  have hbcont : Continuous beta := continuous_actualReferenceBeta g hg L q dr Ar p hL hdr hAr
  have hbpos : ∀ x, 0 < beta x := actualReferenceBeta_pos g hg L q dr Ar p hL hdr hAr hp
  have hu : ContDiff ℝ ∞ U := contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) F
  have h0 (x : R3) (hx : x ∉ K) : U x=0 :=
    highInput_eq_zero_off hO hD F x (fun hy => hx (hsupp hy))
  have hAt (x : R3) (hx : x ∈ K) :=
    hCaps q hq dr hdr hdr1 Ar hAr p hp eta heta he x
      (ball_subset_closedBall (hKball hx)) (hKball hx) (hb x hx) (hs x hx) i l z aa bb cc
  have hA0 (x : R3) (hx : x ∈ K) : ‖A x‖ ≤ Cweight*eta*beta x := by
    have hLift : Cweight*eta ≤ Cweight*eta*beta x := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (hb x hx) (mul_nonneg hCweight.le heta)
    exact (hAt x hx).2.1.trans hLift
  have hGreen := symmetric_first_integral_mass_bound (E := Hi) (F := Hi →L[ℝ] ℝ) EP mu beta U A K hK hm hbcont hbpos
    hu h0 (fun x hx => (hAt x hx).1) (coordinateDirection l)
    Cweight M eta hCweight.le (zero_le_one.trans hM) heta hmu hA0
    (fun x hx => (hAt x hx).2.2 l)
    (fun x hx => hMuCaps q hq x (ball_subset_closedBall (hKball hx)) l)
  have hMass : 0 ≤ ∫ x, mu x*beta x*‖U x‖^2 :=
    integral_nonneg (fun x => mul_nonneg (mul_nonneg (hmu x) (hbpos x).le) (sq_nonneg _))
  refine ⟨hGreen.1,?_⟩
  calc
    _ ≤ (Bgreen*eta)*(∫ x, mu x*beta x*‖U x‖^2) := hGreen.2
    _ ≤ (Bgreen+1)*eta*(∫ x, mu x*beta x*‖U x‖^2) := by
      nlinarith only [mul_nonneg heta hMass]

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSFirstQuadraticActualGreen
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSFirstQuadraticActualGreen.exists_actual_uniform_weighted_triple_symmetric_integral_bound
