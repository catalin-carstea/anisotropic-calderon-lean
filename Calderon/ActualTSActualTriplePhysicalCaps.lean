import Calderon.ActualTSActualTripleRoomCaps
import Calderon.FixedParameterProfileBudgets

/-! Actual physical triple first caps, using the fixed-parameter pullback APIs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Filter Metric
open scoped BigOperators ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSActualTriplePhysicalCaps
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFullEGainedAssembly ActualAllAngularAtomGainedRoom
  ActualFiniteHarmonicCore ConformalDepth ReferenceDensityBounds ReferenceWeightedApproximation
  ActualTSTripleBilinearCoefficient

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "PL" => ActualHigherSScalarCommutatorNativeForm.halfDualPairingL
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete
-- Use the same canonical coefficient instances as `ActualTSActualTripleRoomCaps`.
local notation "Coeff" => ActualTSActualTripleRoomCaps.TripleCoefficientSpace
attribute [local instance] ActualTSActualTripleRoomCaps.tripleCoefficientNormedGroup
  ActualTSActualTripleRoomCaps.tripleCoefficientNormedSpace

/-- Exactly the original three physical conclusions, with the coefficient type fixed once. -/
def PhysicalTripleFirstCaps (A : R3 → Coeff) (x : R3) (bound : ℝ) : Prop :=
  ContDiffAt ℝ ∞ A x ∧ ‖A x‖ ≤ bound ∧ ‖fderiv ℝ A x‖ ≤ bound

theorem physicalTripleFirstCaps_iff (A : R3 → Coeff) (x : R3) (bound : ℝ) :
    PhysicalTripleFirstCaps A x bound ↔
      ContDiffAt ℝ ∞ A x ∧ ‖A x‖ ≤ bound ∧ ‖fderiv ℝ A x‖ ≤ bound := Iff.rfl
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

local notation "Tpar" => (ℝ × (R3 × ℝ)) × (R3 →L[ℝ] ℝ)
local notation "ParamRoom" d:max => Set.prod (commonRoom y0 ρ d) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "KL" => sphereSobolevHalfToSphereL2L hO hD
local notation "AH" => angularAtomHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "AL" => angularAtomLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "RH" => angularAtomReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "RL" => angularAtomReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0



open ActualTSActualTripleRoomCaps FixedParameterProfilePullback FixedParameterProfileBudgets
local notation "QC" => actualTripleCoefficient
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
local notation "Tq" => ActualHigherSFormation.higherSParam L

attribute [local irreducible] actualTripleCoefficient ActualHigherSFormation.higherSParam

/-- Actual original coefficient and genuine spatial derivative caps, with all
constants chosen before profile inputs. -/
theorem exists_actual_uniform_triple_physical_first_caps
    (hL : 0 < L) {d : ℝ} (hd : 0 < d) (P : ARoom d) :
    ∃ Cphys : ℝ, 0 < Cphys ∧ ∃ etaRoom : ℝ, 0 < etaRoom ∧ etaRoom ≤ 1 ∧
      ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, ∀ hAr : 0 < Ar,
      ∀ p : ℕ, 1 ≤ p → ∀ eta : ℝ, 0 ≤ eta → eta ≤ etaRoom →
      ∀ x ∈ closedBall y0 ρ, x ∈ ball y0 ρ →
      1 ≤ actualReferenceBeta g L q dr Ar p x →
      referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta →
      ∀ i j k : AngularAtom,
      PhysicalTripleFirstCaps (fun y => QC ((Tq dr Ar p q) y) i j k) x Cphys := by
  let tripleWitness := exists_actual_uniform_triple_room_first_caps
    hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data hd P
  let Ctri : ℝ := Classical.choose tripleWitness
  have hCtri : 0 < Ctri := (Classical.choose_spec tripleWitness).1
  have hTri := (Classical.choose_spec tripleWitness).2
  obtain ⟨KT,hKT,hTcap⟩ := exists_uniform_higherSParam_derivative_bound
    g hg L hL (closedBall y0 ρ) (isCompact_closedBall _ _)
  obtain ⟨etaRoom,hEta,hEta1,hGuard⟩ := exists_uniform_strict_higherSParam_guard
    g hg L hL y0 ρ d hd (closedBall y0 ρ) (isCompact_closedBall _ _)
  let Cphys : ℝ := Ctri*(KT+1)
  have hCphys : 0 < Cphys := mul_pos hCtri (by linarith only [hKT])
  have hC0 : Ctri ≤ Cphys := by
    dsimp only [Cphys]
    nlinarith only [hCtri,hKT,mul_pos hCtri hKT]
  have hC1 : Ctri*KT ≤ Cphys := by
    dsimp only [Cphys]
    nlinarith only [hCtri]
  refine ⟨Cphys,hCphys,etaRoom,hEta,hEta1,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta hetaRoom x hx hxBall hb hs i j k
  have hguard := hGuard q hq dr hdr hdr1 Ar hAr p hp eta heta hetaRoom x hx hxBall hb hs
  have hmem := higherSParam_eventually_mem y0 ρ d L dr Ar q p hdr hAr x hguard
  have hWithin := hTri i j k
  have hAt := higherSParam_pullback (fun t => QC t i j k) y0 ρ d L dr Ar q p
    hdr hAr x hWithin.1 hguard
  have hD := hTcap q hq dr hdr hdr1 Ar hAr p hp eta heta
    (hetaRoom.trans hEta1) x hx hb hs
  have hPair := hWithin.2 ((Tq dr Ar p q) x) hmem.self_of_nhds
  refine ⟨hAt.1,hPair.1.trans hC0,?_⟩
  exact (hAt.2.trans (mul_le_mul hPair.2 hD (ContinuousLinearMap.opNorm_nonneg (fderiv ℝ (Tq dr Ar p q) x)) hCtri.le)).trans hC1

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSActualTriplePhysicalCaps
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSActualTriplePhysicalCaps.exists_actual_uniform_triple_physical_first_caps
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSActualTriplePhysicalCaps.physicalTripleFirstCaps_iff
