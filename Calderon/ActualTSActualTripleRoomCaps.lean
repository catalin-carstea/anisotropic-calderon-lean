import Calderon.ActualTSTripleBilinearCoefficient

/-! Actual original all-angular-room triple coefficient first within caps.
No ambient differentiability is inferred from the closed parameter room. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Filter Metric
open scoped BigOperators ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSActualTripleRoomCaps
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFullEGainedAssembly ActualAllAngularAtomGainedRoom
  ActualFiniteHarmonicCore ConformalDepth ReferenceDensityBounds ReferenceWeightedApproximation
  ActualTSTripleBilinearCoefficient

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "PL" => ActualHigherSScalarCommutatorNativeForm.halfDualPairingL
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete
@[instance_reducible] private def highNormed : NormedAddCommGroup (Hi →L[ℝ] Half) := inferInstance
@[instance_reducible] private def highSpace : NormedSpace ℝ (Hi →L[ℝ] Half) := inferInstance
@[instance_reducible] private def lowNormed : NormedAddCommGroup (Half →L[ℝ] Neg) := inferInstance
@[instance_reducible] private def lowSpace : NormedSpace ℝ (Half →L[ℝ] Neg) := inferInstance
@[instance_reducible] private def negDualNormed : NormedAddCommGroup (Neg →L[ℝ] ℝ) := inferInstance
@[instance_reducible] private def negDualSpace : NormedSpace ℝ (Neg →L[ℝ] ℝ) := inferInstance
attribute [local instance] highNormed highSpace lowNormed lowSpace negDualNormed negDualSpace
@[instance_reducible] private def highDualNormed : NormedAddCommGroup (Hi →L[ℝ] ℝ) := inferInstance
@[instance_reducible] private def highDualSpace : NormedSpace ℝ (Hi →L[ℝ] ℝ) := inferInstance
attribute [local instance] highDualNormed highDualSpace
@[instance_reducible] private def tripleNormed : NormedAddCommGroup (Hi →L[ℝ] Hi →L[ℝ] ℝ) := inferInstance
@[instance_reducible] private def tripleSpace : NormedSpace ℝ (Hi →L[ℝ] Hi →L[ℝ] ℝ) := inferInstance
attribute [local instance] tripleNormed tripleSpace
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


/-- The identical original ordered triple pairing as a bounded bilinear coefficient. -/
def actualTripleCoefficient (t : Tpar) (i j k : AngularAtom) : Hi →L[ℝ] Hi →L[ℝ] ℝ :=
  tripleCoefficient PL (AH t i) (AL t j) (AH t k)
local notation "QC" => actualTripleCoefficient
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0

attribute [local irreducible] angularAtomHigh angularAtomLow angularAtomReverseHigh
  angularAtomReverseLow ActualHigherSScalarCommutatorNativeForm.halfDualPairingL

/-- Original smoothness/caps and standard room geometry close every premise internally. -/
theorem exists_actual_uniform_triple_room_first_caps {d : ℝ} (hd : 0 < d) (P : ARoom d) :
    ∃ Ctriple : ℝ, 0 < Ctriple ∧ ∀ i j k : AngularAtom,
      ContDiffOn ℝ ∞ (fun t => QC t i j k) (ParamRoom d) ∧
      ∀ t ∈ ParamRoom d, ‖QC t i j k‖ ≤ Ctriple ∧
        ‖fderivWithin ℝ (fun s => QC s i j k) (ParamRoom d) t‖ ≤ Ctriple := by
  have hUD : UniqueDiffOn ℝ (ParamRoom d) :=
    (uniqueDiffOn_commonRoom y0 ρ hData.1.2.1 hd).prod
      (uniqueDiffOn_convex (convex_closedBall _ _)
        ⟨0,ball_subset_interior_closedBall (mem_ball_self one_pos)⟩)
  let caps := P.finiteCaps 1
  let M : ℝ := Classical.choose caps
  have hM : 1 ≤ M := (Classical.choose_spec caps).1
  have hAtoms := (Classical.choose_spec caps).2.1
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hN : 0 ≤ ‖PL‖ := ContinuousLinearMap.opNorm_nonneg PL
  let Ctriple : ℝ := 1+3*(‖PL‖+1)*M^3
  have hCtriple : 0 < Ctriple := by dsimp only [Ctriple]; positivity
  have hLast : 3*(‖PL‖+1)*M^3 ≤ Ctriple := le_add_of_nonneg_left zero_le_one
  have h0 : ‖PL‖*M^3 ≤ Ctriple :=
    (mul_le_mul_of_nonneg_right (by linarith only [hN] : ‖PL‖ ≤ 3*(‖PL‖+1))
      (pow_nonneg hM0 _)).trans hLast
  have h1 : 3*‖PL‖*M^3 ≤ Ctriple :=
    (mul_le_mul_of_nonneg_right (by linarith : 3*‖PL‖ ≤ 3*(‖PL‖+1))
      (pow_nonneg hM0 _)).trans hLast
  refine ⟨Ctriple,hCtriple,?_⟩
  intro i j k
  have hAi := (P.atomSmooth i).1
  have hBj := (P.atomSmooth j).2.1
  have hCk := (P.atomSmooth k).1
  constructor
  · exact contDiffOn_tripleCoefficient PL (fun s => AH s i) (fun s => AH s k)
      (fun s => AL s j) (ParamRoom d) hAi hBj hCk
  · intro t ht
    have hAi0 : ‖AH t i‖ ≤ M := by
      simpa only [norm_iteratedFDerivWithin_zero] using (hAtoms i 0 (by norm_num) t ht).1
    have hBj0 : ‖AL t j‖ ≤ M := by
      simpa only [norm_iteratedFDerivWithin_zero] using (hAtoms j 0 (by norm_num) t ht).2.1
    have hCk0 : ‖AH t k‖ ≤ M := by
      simpa only [norm_iteratedFDerivWithin_zero] using (hAtoms k 0 (by norm_num) t ht).1
    have hAi1 : ‖fderivWithin ℝ (fun s => AH s i) (ParamRoom d) t‖ ≤ M := by
      simpa only [norm_iteratedFDerivWithin_one _ (hUD t ht)] using (hAtoms i 1 le_rfl t ht).1
    have hBj1 : ‖fderivWithin ℝ (fun s => AL s j) (ParamRoom d) t‖ ≤ M := by
      simpa only [norm_iteratedFDerivWithin_one _ (hUD t ht)] using (hAtoms j 1 le_rfl t ht).2.1
    have hCk1 : ‖fderivWithin ℝ (fun s => AH s k) (ParamRoom d) t‖ ≤ M := by
      simpa only [norm_iteratedFDerivWithin_one _ (hUD t ht)] using (hAtoms k 1 le_rfl t ht).1
    have hCaps := tripleCoefficient_within_first_caps PL (fun s => AH s i) (fun s => AH s k)
      (fun s => AL s j) (ParamRoom d) t (hUD t ht)
      (hAi.differentiableOn (by simp) t ht) (hBj.differentiableOn (by simp) t ht)
      (hCk.differentiableOn (by simp) t ht) M hM0 hAi0 hBj0 hCk0 hAi1 hBj1 hCk1
    exact ⟨hCaps.1.trans h0,hCaps.2.trans h1⟩


/-- Named carrier for the identical original bounded bilinear coefficient.
This abbreviation captures the existing nested continuous-linear-map instances. -/
abbrev TripleCoefficientSpace : Type := Hi →L[ℝ] Hi →L[ℝ] ℝ

/-- Export the original canonical instance used by the room theorem. -/
@[instance_reducible] def tripleCoefficientNormedGroup :
    NormedAddCommGroup TripleCoefficientSpace := tripleNormed
@[instance_reducible] def tripleCoefficientNormedSpace :
    NormedSpace ℝ TripleCoefficientSpace := tripleSpace
@[instance_reducible] def spatialTripleCoefficientNormedGroup :
    NormedAddCommGroup (R3 →L[ℝ] TripleCoefficientSpace) := inferInstance
@[instance_reducible] def spatialTripleCoefficientNormedSpace :
    NormedSpace ℝ (R3 →L[ℝ] TripleCoefficientSpace) := inferInstance

/-- The exported norm is definitionally the original coefficient norm. -/
theorem tripleCoefficient_norm_transport (v : TripleCoefficientSpace) :
    (letI := tripleCoefficientNormedGroup; ‖v‖) = ‖v‖ := rfl

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSActualTripleRoomCaps
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSActualTripleRoomCaps.exists_actual_uniform_triple_room_first_caps

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSActualTripleRoomCaps.tripleCoefficient_norm_transport
