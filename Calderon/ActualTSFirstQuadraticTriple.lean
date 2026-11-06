import Calderon.ActualTSZeroWordPairing

/-! Three-word first-T/quadratic-S angular symmetrization with its genuine
included-derivative gained error. The symmetric weighted base form remains open.
Before-code: ../T-first-S-quadratic-triple-before-source-nov03-night-v001/. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Filter Metric
open scoped BigOperators ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSFirstQuadraticTriple
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFullEGainedAssembly ActualAllAngularAtomGainedRoom
  ActualFiniteHarmonicCore ConformalDepth ReferenceDensityBounds ReferenceWeightedApproximation

section Generic
variable {ι H E F G : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

private lemma reverse_triple_eq (P : E →L[ℝ] F →L[ℝ] ℝ) (J : E →L[ℝ] F)
    (A R : ι → H →L[ℝ] E) (AL RL : ι → E →L[ℝ] F) (GH : ι → ι → H →L[ℝ] E)
    (hPivot : ∀ i (z y : E), P z (AL i y)=P y (RL i z))
    (hGain : ∀ i j u, J (GH i j u)=RL i (A j u)-AL j (R i u))
    (i j k : ι) (u v : H) :
    P (R i v) (RL k (R j u)) =
      P (A i u) (AL j (A k v))-
        P (A k v) (J (GH j i u))-P (R j u) (J (GH i k v)) := by
  have hIK : AL k (R i v)=RL i (A k v)-J (GH i k v) :=
    eq_sub_iff_add_eq.mpr ((add_comm _ _).trans (eq_sub_iff_add_eq.mp (hGain i k v)))
  have hJI : AL i (R j u)=RL j (A i u)-J (GH j i u) :=
    eq_sub_iff_add_eq.mpr ((add_comm _ _).trans (eq_sub_iff_add_eq.mp (hGain j i u)))
  calc
    _ = P (R j u) (AL k (R i v)) := (hPivot k (R j u) (R i v)).symm
    _ = P (R j u) (RL i (A k v))-P (R j u) (J (GH i k v)) := by rw [hIK,map_sub]
    _ = P (A k v) (AL i (R j u))-P (R j u) (J (GH i k v)) :=
      congrArg (fun z : ℝ => z-P (R j u) (J (GH i k v))) (hPivot i (A k v) (R j u)).symm
    _ = (P (A k v) (RL j (A i u))-P (A k v) (J (GH j i u)))-
        P (R j u) (J (GH i k v)) := by rw [hJI,map_sub]
    _ = _ := congrArg (fun z : ℝ => z-P (A k v) (J (GH j i u))-P (R j u) (J (GH i k v)))
      (hPivot j (A i u) (A k v)).symm

/-- Exact sign/order of the odd three-word reverse sum, before base integration. -/
theorem triple_pairing_plus_reverse_eq_symmetrized_sub_gains
    (P : E →L[ℝ] F →L[ℝ] ℝ) (J : E →L[ℝ] F)
    (A R : ι → H →L[ℝ] E) (AL RL : ι → E →L[ℝ] F) (GH : ι → ι → H →L[ℝ] E)
    (hPivot : ∀ i (z y : E), P z (AL i y)=P y (RL i z))
    (hGain : ∀ i j u, J (GH i j u)=RL i (A j u)-AL j (R i u))
    (i j k : ι) (u v : H) :
    P (A i v) (AL j (A k u))+P (R i v) (RL k (R j u)) =
      P (A i v) (AL j (A k u))+P (A i u) (AL j (A k v))-
        (P (A k v) (J (GH j i u))+P (R j u) (J (GH i k v))) := by
  rw [reverse_triple_eq P J A R AL RL GH hPivot hGain i j k u v]
  ring

private lemma bilinear_action_bound (P : E →L[ℝ] F →L[ℝ] ℝ)
    (A : H →L[ℝ] E) (B : G →L[ℝ] F) (u : H) (v : G)
    (N M : ℝ) (hN : 0 ≤ N) (hM : 0 ≤ M) (hP : ‖P‖ ≤ N)
    (hA : ‖A‖ ≤ M) (hB : ‖B‖ ≤ M) :
    |P (A u) (B v)| ≤ N*M^2*‖u‖*‖v‖ := by
  have hAv : ‖A u‖ ≤ M*‖u‖ :=
    (A.le_opNorm u).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg u))
  have hBv : ‖B v‖ ≤ M*‖v‖ :=
    (B.le_opNorm v).trans (mul_le_mul_of_nonneg_right hB (norm_nonneg v))
  have hPair : |P (A u) (B v)| ≤ ‖P‖*‖A u‖*‖B v‖ := by
    simpa only [Real.norm_eq_abs] using ContinuousLinearMap.le_opNorm₂ P (A u) (B v)
  exact (hPair.trans (mul_le_mul (mul_le_mul hP hAv (norm_nonneg _) hN) hBv
    (norm_nonneg _) (mul_nonneg hN (mul_nonneg hM (norm_nonneg _))))).trans_eq (by ring)

/-- Both gained terms use IH(v), never the unavailable high derivative norm. -/
theorem triple_pairing_gain_error_bound
    (P : E →L[ℝ] F →L[ℝ] ℝ) (I : H →L[ℝ] G) (J : E →L[ℝ] F)
    (A R : ι → H →L[ℝ] E) (AL : ι → G →L[ℝ] F)
    (GH : ι → ι → H →L[ℝ] E) (GainL : ι → ι → G →L[ℝ] F)
    (hSym : ∀ z y : E, P z (J y)=P y (J z))
    (hA : ∀ i v, J (A i v)=AL i (I v))
    (hGainL : ∀ i j v, GainL i j (I v)=J (GH i j v))
    (N M : ℝ) (hN : 0 ≤ N) (hM : 0 ≤ M) (hP : ‖P‖ ≤ N)
    (hRH : ∀ i, ‖R i‖ ≤ M) (hAL : ∀ i, ‖AL i‖ ≤ M)
    (hGH : ∀ i j, ‖GH i j‖ ≤ M) (hLow : ∀ i j, ‖GainL i j‖ ≤ M)
    (i j k : ι) (u v : H) :
    |P (A k v) (J (GH j i u))+P (R j u) (J (GH i k v))| ≤
      (2*N*M^2)*‖u‖*‖I v‖ := by
  have he1 : P (A k v) (J (GH j i u))=P (GH j i u) (AL k (I v)) :=
    (hSym _ _).trans (congrArg (P (GH j i u)) (hA k v))
  have he2 : P (R j u) (J (GH i k v))=P (R j u) (GainL i k (I v)) :=
    congrArg (P (R j u)) (hGainL i k v).symm
  rw [he1,he2]
  have h1 := bilinear_action_bound P (GH j i) (AL k) u (I v)
    N M hN hM hP (hGH j i) (hAL k)
  have h2 := bilinear_action_bound P (R j) (GainL i k) u (I v)
    N M hN hM hP (hRH j) (hLow i k)
  have hs : |P (GH j i u) (AL k (I v))+P (R j u) (GainL i k (I v))| ≤
      |P (GH j i u) (AL k (I v))|+|P (R j u) (GainL i k (I v))| := by
    simpa only [Real.norm_eq_abs] using norm_add_le
      (P (GH j i u) (AL k (I v))) (P (R j u) (GainL i k (I v)))
  exact (hs.trans (add_le_add h1 h2)).trans_eq (by ring)
end Generic

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "PL" => ActualHigherSScalarCommutatorNativeForm.halfDualPairingL
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete
@[instance_reducible] private def highNormed : NormedAddCommGroup (Hi →L[ℝ] Half) := inferInstance
@[instance_reducible] private def highSpace : NormedSpace ℝ (Hi →L[ℝ] Half) := inferInstance
@[instance_reducible] private def lowNormed : NormedAddCommGroup (Half →L[ℝ] Neg) := inferInstance
@[instance_reducible] private def lowSpace : NormedSpace ℝ (Half →L[ℝ] Neg) := inferInstance
attribute [local instance] highNormed highSpace lowNormed lowSpace
@[instance_reducible] private def negDualNormed : NormedAddCommGroup (Neg →L[ℝ] ℝ) := inferInstance
@[instance_reducible] private def negDualSpace : NormedSpace ℝ (Neg →L[ℝ] ℝ) := inferInstance
attribute [local instance] negDualNormed negDualSpace
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


attribute [local irreducible] angularAtomHigh angularAtomLow angularAtomReverseHigh
  angularAtomReverseLow sphereSobolevInclusionL ActualHigherSScalarCommutatorNativeForm.halfDualPairingL

/-- Every graph, pivot, symmetry and norm premise is produced by the original room. -/
theorem exists_actual_uniform_three_word_symmetrization {d : ℝ} (P : ARoom d) :
    ∃ Cgain : ℝ, 0 < Cgain ∧ ∀ t ∈ ParamRoom d, ∀ u v : Hi, ∀ i j k : AngularAtom,
      (PL (AH t i v) (AL t j (AH t k u))+PL (RH t i v) (RL t k (RH t j u)) =
        PL (AH t i v) (AL t j (AH t k u))+PL (AH t i u) (AL t j (AH t k v))-
          (PL (AH t k v) (JL (P.gainHigh j i t u))+
            PL (RH t j u) (JL (P.gainHigh i k t v)))) ∧
      |PL (AH t k v) (JL (P.gainHigh j i t u))+
          PL (RH t j u) (JL (P.gainHigh i k t v))| ≤ Cgain*‖u‖*‖IH v‖ := by
  let caps := P.finiteCaps 0
  let M := Classical.choose caps
  have hM : 1 ≤ M := (Classical.choose_spec caps).1
  have hAtoms := (Classical.choose_spec caps).2.1
  have hGains := (Classical.choose_spec caps).2.2
  let N : ℝ := ‖PL‖+1
  have hN : 0 < N := by dsimp only [N]; positivity
  have hMpos : 0 < M := zero_lt_one.trans_le hM
  have hC : 0 < 2*N*M^2 := by positivity
  refine ⟨2*N*M^2,hC,?_⟩
  intro t ht u v i j k
  have hPivot (b : AngularAtom) (z y : Half) : PL z (AL t b y)=PL y (RL t b z) := by
    simpa only [ActualHigherSScalarCommutatorNativeForm.halfDualPairingL_apply] using
      P.atomPivot b t ht z y
  have hGain (b e : AngularAtom) (z : Hi) :
      JL (P.gainHigh b e t z)=RL t b (AH t e z)-AL t e (RH t b z) :=
    P.gainGraph b e t ht z
  have hSym (z y : Half) : PL z (JL y)=PL y (JL z) := by
    rw [ActualHigherSZeroAtomTransport.half_pairing_inner hO hD,
      ActualHigherSZeroAtomTransport.half_pairing_inner hO hD]
    exact real_inner_comm _ _
  have hAG (b : AngularAtom) (z : Hi) : JL (AH t b z)=AL t b (IH z) :=
    P.atomGraph b t ht z
  have hGainL (b e : AngularAtom) (z : Hi) : P.gainLow b e t (IH z)=JL (P.gainHigh b e t z) := by
    simpa only [ContinuousLinearMap.comp_apply] using
      congrArg (fun K : Hi →L[ℝ] Neg => K z) (P.upper b e t ht)
  have hRH (b : AngularAtom) : ‖RH t b‖ ≤ M := by
    simpa only [norm_iteratedFDerivWithin_zero] using (hAtoms b 0 le_rfl t ht).2.2.1
  have hAL (b : AngularAtom) : ‖AL t b‖ ≤ M := by
    simpa only [norm_iteratedFDerivWithin_zero] using (hAtoms b 0 le_rfl t ht).2.1
  have hGH (b e : AngularAtom) : ‖P.gainHigh b e t‖ ≤ M := by
    simpa only [norm_iteratedFDerivWithin_zero] using (hGains b e 0 le_rfl t ht).1
  have hLow (b e : AngularAtom) : ‖P.gainLow b e t‖ ≤ M := by
    simpa only [norm_iteratedFDerivWithin_zero] using (hGains b e 0 le_rfl t ht).2
  constructor
  · exact triple_pairing_plus_reverse_eq_symmetrized_sub_gains
      PL JL (AH t) (RH t) (AL t) (RL t) (fun b e => P.gainHigh b e t) hPivot hGain i j k u v
  · exact triple_pairing_gain_error_bound PL IH JL (AH t) (RH t) (AL t)
      (fun b e => P.gainHigh b e t) (fun b e => P.gainLow b e t)
      hSym hAG hGainL N M hN.le hMpos.le (by dsimp only [N]; linarith)
      hRH hAL hGH hLow i j k u v

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSFirstQuadraticTriple
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSFirstQuadraticTriple.exists_actual_uniform_three_word_symmetrization
