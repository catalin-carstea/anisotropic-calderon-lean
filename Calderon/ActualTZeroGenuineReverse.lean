import Calderon.ActualAllAngularAtomGainedRoom
import Calderon.ActualReferenceZeroECommutators
import Calderon.ActualFixedAtomFiniteLifts

/-!
Exact original RAW Tdag-zero versus genuine reversed angular words.
The original N-1 correction is retained explicitly. This is not an energy bound
or the whole signed T/S estimate.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Filter Metric
open scoped BigOperators ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTZeroGenuineReverse
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFullEGainedAssembly ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualGeneratorEPairedGainedEndpoints ActualRetainedGeneratorMultiplierGains
  ActualTZeroNegativeGraph ActualReferenceZeroECommutators ActualAllAngularAtomGainedRoom
  ActualFixedAtomFiniteLifts SmoothMetricFrame MovingFrameConnection AmbientReferenceRaising
  ReferenceDensityBounds ConformalDepth

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "DL" => sphereSobolevShiftedDegreeL (3/2 : ℝ)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete
@[instance_reducible] private def highHalfNormed : NormedAddCommGroup (Hi →L[ℝ] Half) := inferInstance
@[instance_reducible] private def highHalfSpace : NormedSpace ℝ (Hi →L[ℝ] Half) := inferInstance
@[instance_reducible] private def highNegNormed : NormedAddCommGroup (Hi →L[ℝ] Neg) := inferInstance
@[instance_reducible] private def highNegSpace : NormedSpace ℝ (Hi →L[ℝ] Neg) := inferInstance
attribute [local instance] highHalfNormed highHalfSpace highNegNormed highNegSpace

private lemma finite_weighted_exchange {ι κ E F : Type*}
    [Fintype ι] [Fintype κ]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (J : E →L[ℝ] F) (c : ι → κ → ℝ) (s : κ → ℝ) (f : ι → ℝ)
    (A B : ι → κ → F) (G : ι → κ → E) (a : ι → E)
    (h : ∀ i V, A i V=B i V+J (s V • G i V)) :
    (∑ i, ((∑ V, c i V • A i V)-f i • J (a i))) =
      (∑ i, ∑ V, c i V • B i V)+
        J ((∑ i, ∑ V, (c i V*s V) • G i V)-∑ i, f i • a i) := by
  classical
  simp_rw [h]
  simp only [map_sub,map_sum,map_smul,smul_add,smul_smul,
    Finset.sum_add_distrib,Finset.sum_sub_distrib]
  abel

private def generatorSign : Generator → ℝ
  | Sum.inl _ => -1
  | Sum.inr _ => 1

private lemma sharpHigh_eq_sign (V : Generator) :
    generatorSharpHigh V=generatorSign V • generatorHigh V := by
  cases V <;> simp only [generatorSign,generatorSharpHigh,neg_one_smul,one_smul]

private lemma sharpLow_eq_sign (V : Generator) :
    generatorSharpLow V=generatorSign V • generatorLow V := by
  cases V <;> simp only [generatorSign,generatorSharpLow,neg_one_smul,one_smul]

variable (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (g : MatrixField) (L : ℝ)
local notation "cc" => referenceAngularZeroCoefficient g L
local notation "fi" q:max dr:max Ar:max p:max x:max i:max =>
  referenceFrameDerivative g L q i (fun y => Real.log (referenceRadius dr Ar p L y)) x
local notation "aH" => loweringHigh hF hO hD
local notation "aL" => loweringLow hF hO hD

/-- Genuine reversed quadratic T-zero words; this is NOT raw nativeTdag-zero. -/
def genuineReferenceZeroReverseNegative (q dr Ar : ℝ) (p : ℕ) (x : R3) : Hi →L[ℝ] Neg :=
  ∑ i : Fin 3, ∑ V : Generator, cc q dr Ar p x i V • (generatorSharpLow V).comp (aH i)

/-- Genuine reversed words on the original finite input, using only its existing finite lifts. -/
def genuineReferenceZeroReverseHalf (q dr Ar : ℝ) (p : ℕ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : Half :=
  ∑ i : Fin 3, ∑ V : Generator, cc q dr Ar p x i V •
    generatorSharpHigh V (loweringFiniteHi hF hO hD F i x)

local notation "RNeg" => genuineReferenceZeroReverseNegative hF hO hD g L
local notation "RHalf" => genuineReferenceZeroReverseHalf hF hO hD g L

variable (y0 : R3) (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3))
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
local notation "Tq" => ActualHigherSFormation.higherSParam L
local notation "ParamRoom" d:max => Set.prod (commonRoom y0 ρ d) (closedBall (0 : R3 →L[ℝ] ℝ) 1)

/-- Exact lower-order correction: all gained generator/lowering terms AND the original -fi term. -/
def referenceZeroAdjointCorrection {d : ℝ} (P : ARoom d)
    (q dr Ar : ℝ) (p : ℕ) (x : R3) : Hi →L[ℝ] Half :=
  (∑ i : Fin 3, ∑ V : Generator,
    (cc q dr Ar p x i V*generatorSign V) •
      P.gainHigh (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inl V)) ((Tq dr Ar p q) x))-
    ∑ i : Fin 3, fi q dr Ar p x i • aH i
local notation "Corr" => referenceZeroAdjointCorrection
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data

attribute [local irreducible] generatorHigh generatorLow generatorSharpHigh generatorSharpLow
  angularAtomHigh angularAtomLow angularAtomReverseHigh angularAtomReverseLow
  loweringHigh loweringLow referenceHighHorizontalAngularL sphereSobolevShiftedDegreeL
  sphereSobolevInclusionL referenceAdjointZeroNegative referenceAngularSharpHigh
  genuineReferenceZeroReverseNegative referenceZeroAdjointCorrection


/-- Scalar bookkeeping for the EXACT correction, in its original operator norm, with the scalar
and atom budgets as hypotheses; they are produced in the uniform consumer. -/
theorem norm_referenceZeroAdjointCorrection_le {d : ℝ} (P : ARoom d)
    (q dr Ar : ℝ) (p : ℕ) (x : R3) (S M beta : ℝ)
    (hS : 0 ≤ S) (hM : 0 ≤ M) (hb : 0 ≤ beta)
    (hc : ∀ i : Fin 3, ∀ V : Generator, |cc q dr Ar p x i V| ≤ S*beta)
    (hf : ∀ i : Fin 3, |fi q dr Ar p x i| ≤ S*beta)
    (hG : ∀ i : Fin 3, ∀ V : Generator,
      ‖P.gainHigh (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inl V)) ((Tq dr Ar p q) x)‖ ≤ M)
    (ha : ∀ i : Fin 3, ‖aH i‖ ≤ M) :
    ‖Corr P q dr Ar p x‖ ≤ 33*S*M*beta := by
  have hSign (V : Generator) : |generatorSign V|=1 := by
    cases V <;> norm_num [generatorSign]
  have hTerm (i : Fin 3) (V : Generator) :
      ‖(cc q dr Ar p x i V*generatorSign V) •
        P.gainHigh (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inl V)) ((Tq dr Ar p q) x)‖ ≤
        (S*beta)*M := by
    rw [norm_smul,Real.norm_eq_abs,abs_mul,hSign,mul_one]
    exact mul_le_mul (hc i V) (hG i V) (norm_nonneg _) (mul_nonneg hS hb)
  have hFirst :
      ‖∑ i : Fin 3, ∑ V : Generator,
        (cc q dr Ar p x i V*generatorSign V) •
          P.gainHigh (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inl V)) ((Tq dr Ar p q) x)‖ ≤
      30*S*M*beta := by
    calc
      _ ≤ ∑ i : Fin 3, ‖∑ V : Generator,
          (cc q dr Ar p x i V*generatorSign V) •
            P.gainHigh (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inl V)) ((Tq dr Ar p q) x)‖ := norm_sum_le _ _
      _ ≤ ∑ i : Fin 3, ∑ V : Generator,
          ‖(cc q dr Ar p x i V*generatorSign V) •
            P.gainHigh (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inl V)) ((Tq dr Ar p q) x)‖ :=
        Finset.sum_le_sum (fun i _ => norm_sum_le _ _)
      _ ≤ ∑ _i : Fin 3, ∑ _V : Generator, (S*beta)*M :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun V _ => hTerm i V))
      _ = 30*S*M*beta := by
        norm_num [Generator,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
        <;> ring
  have hSecond : ‖∑ i : Fin 3, fi q dr Ar p x i • aH i‖ ≤ 3*S*M*beta := by
    calc
      _ ≤ ∑ i : Fin 3, ‖fi q dr Ar p x i • aH i‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin 3, (S*beta)*M := Finset.sum_le_sum (fun i _ => by
        rw [norm_smul,Real.norm_eq_abs]
        exact mul_le_mul (hf i) (ha i) (norm_nonneg _) (mul_nonneg hS hb))
      _ = 3*S*M*beta := by
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
        ring
  unfold referenceZeroAdjointCorrection
  exact (norm_sub_le _ _).trans ((add_le_add hFirst hSecond).trans_eq (by ring))

private lemma genuine_reverse_negative_apply
    (q dr Ar : ℝ) (p : ℕ) (x : R3) (U : Hi) :
    RNeg q dr Ar p x U =
      ∑ i : Fin 3, ∑ V : Generator, cc q dr Ar p x i V • generatorSharpLow V (aH i U) := by
  simp only [genuineReferenceZeroReverseNegative,_root_.sum_apply,_root_.smul_apply,
    ContinuousLinearMap.comp_apply]

private lemma adjoint_correction_apply {d : ℝ} (P : ARoom d)
    (q dr Ar : ℝ) (p : ℕ) (x : R3) (U : Hi) :
    Corr P q dr Ar p x U =
      (∑ i : Fin 3, ∑ V : Generator, (cc q dr Ar p x i V*generatorSign V) •
        P.gainHigh (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inl V)) ((Tq dr Ar p q) x) U)-
      ∑ i : Fin 3, fi q dr Ar p x i • aH i U := by
  simp only [referenceZeroAdjointCorrection,_root_.sum_apply,_root_.smul_apply,_root_.sub_apply]

/-- Exact raw N-1 identity; no correction is silently dropped or assigned to Z. -/
theorem raw_adjoint_zero_eq_genuine_reverse_add_correction
    {d : ℝ} (P : ARoom d) (q dr Ar : ℝ) (p : ℕ) (x : R3)
    (ht : (Tq dr Ar p q) x ∈ ParamRoom d) (U : Hi) :
    referenceAdjointZeroNegative hO hD hF g L q dr Ar p x U =
      RNeg q dr Ar p x U+JL (Corr P q dr Ar p x U) := by
  let t := (Tq dr Ar p q) x
  have hGain (i : Fin 3) (V : Generator) :
      JL (P.gainHigh (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inl V)) t U) =
        aL i (generatorHigh V U)-generatorLow V (aH i U) := by
    simpa only [angularAtomHigh,angularAtomLow,angularAtomReverseHigh,angularAtomReverseLow] using
      P.gainGraph (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inl V)) t ht U
  have hRow (i : Fin 3) (V : Generator) :
      aL i (generatorSharpHigh V U)=generatorSharpLow V (aH i U)+
        JL (generatorSign V • P.gainHigh (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inl V)) t U) := by
    have hBase : aL i (generatorHigh V U)=generatorLow V (aH i U)+
        JL (P.gainHigh (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inl V)) t U) := by
      rw [hGain]
      abel
    have hHi : generatorSharpHigh V U=generatorSign V • generatorHigh V U :=
      congrArg (fun K : Hi →L[ℝ] Half => K U) (sharpHigh_eq_sign V)
    have hLo : generatorSharpLow V (aH i U)=generatorSign V • generatorLow V (aH i U) :=
      congrArg (fun K : Half →L[ℝ] Neg => K (aH i U)) (sharpLow_eq_sign V)
    calc
      _ = aL i (generatorSign V • generatorHigh V U) := congrArg (aL i) hHi
      _ = generatorSign V • aL i (generatorHigh V U) := map_smul _ _ _
      _ = generatorSign V • (generatorLow V (aH i U)+
          JL (P.gainHigh (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inl V)) t U)) :=
        congrArg (fun z : Neg => generatorSign V • z) hBase
      _ = generatorSign V • generatorLow V (aH i U)+
          JL (generatorSign V • P.gainHigh (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inl V)) t U) := by
        simp only [smul_add,map_smul]
      _ = _ := congrArg (fun z : Neg => z+
        JL (generatorSign V • P.gainHigh (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inl V)) t U)) hLo.symm
  have hFactor (i : Fin 3) :
      (-referenceHighHorizontalAngularL g L q x i+
          fi q dr Ar p x i • (DL-IH)) U =
      (∑ V : Generator, cc q dr Ar p x i V • generatorSharpHigh V U)-
        fi q dr Ar p x i • IH U := by
    have hSharp : referenceAngularSharpHigh g L q dr Ar p x i =
        -referenceHighHorizontalAngularL g L q x i+fi q dr Ar p x i • DL :=
      referenceAngularSharpHigh_eq g L q dr Ar p x i
    have hAlg : -referenceHighHorizontalAngularL g L q x i+
        fi q dr Ar p x i • (DL-IH) =
        (-referenceHighHorizontalAngularL g L q x i+fi q dr Ar p x i • DL)-
          fi q dr Ar p x i • IH := by
      simp only [smul_sub]
      abel
    have hMap := hAlg.trans (congrArg (fun K : Hi →L[ℝ] Half =>
      K-fi q dr Ar p x i • IH) hSharp.symm)
    have hEval := congrArg (fun K : Hi →L[ℝ] Half => K U) hMap
    exact hEval.trans (by
      simp only [referenceAngularSharpHigh,_root_.sub_apply,_root_.sum_apply,_root_.smul_apply])
  have hLower (i : Fin 3) : aL i (IH U)=JL (aH i U) := by
    simpa only [angularAtomReverseHigh,angularAtomReverseLow] using
      (P.reverseAtomGraph (Sum.inr (Sum.inr i)) t ht U).symm
  calc
    _ = ∑ i : Fin 3, ((∑ V : Generator, cc q dr Ar p x i V • aL i (generatorSharpHigh V U))-
        fi q dr Ar p x i • aL i (IH U)) := by
      simp only [referenceAdjointZeroNegative,_root_.sum_apply,ContinuousLinearMap.comp_apply]
      simp_rw [hFactor]
      simp only [map_sub,map_sum,map_smul]
    _ = (∑ i : Fin 3, ∑ V : Generator,
          cc q dr Ar p x i V • generatorSharpLow V (aH i U))+
        JL ((∑ i : Fin 3, ∑ V : Generator, (cc q dr Ar p x i V*generatorSign V) •
          P.gainHigh (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inl V)) t U)-
          ∑ i : Fin 3, fi q dr Ar p x i • aH i U) := by
      simp_rw [hLower]
      exact finite_weighted_exchange JL (cc q dr Ar p x) generatorSign
        (fun i => fi q dr Ar p x i)
        (fun i V => aL i (generatorSharpHigh V U))
        (fun i V => generatorSharpLow V (aH i U))
        (fun i V => P.gainHigh (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inl V)) t U)
        (fun i => aH i U) hRow
    _ = RNeg q dr Ar p x U+JL (Corr P q dr Ar p x U) :=
      congrArg₂ (fun u v : Neg => u+v)
        (genuine_reverse_negative_apply hF hO hD g L q dr Ar p x U).symm
        (congrArg JL (adjoint_correction_apply
          hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data
          P q dr Ar p x U).symm)

/-- Genuine reversed finite words have exactly the original reversed negative graph. -/
theorem genuine_reverse_half_negative_graph {d : ℝ} (P : ARoom d)
    (q dr Ar : ℝ) (p : ℕ) (F : smoothCompactFiniteSphereCore hO hD) (x : R3)
    (ht : (Tq dr Ar p q) x ∈ ParamRoom d) :
    JL (RHalf q dr Ar p F x)=
      RNeg q dr Ar p x (finiteCoreSobolevLift hO hD (3/2 : ℝ) F x) := by
  have hGen (V : Generator) (v : Hi) :
      JL (generatorSharpHigh V v)=generatorSharpLow V (IH v) := by
    simpa only [angularAtomReverseHigh,angularAtomReverseLow] using
      P.reverseAtomGraph (Sum.inr (Sum.inl V)) ((Tq dr Ar p q) x) ht v
  simp only [genuineReferenceZeroReverseHalf,genuineReferenceZeroReverseNegative,map_sum,map_smul,
    _root_.sum_apply,_root_.smul_apply,ContinuousLinearMap.comp_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro V _
  rw [hGen,loweringFiniteHi_inclusion]

/-- The actual original finite raw Tdag-zero Half field, with its full correction. -/
theorem native_raw_adjoint_zero_half_eq_genuine_reverse_add_correction
    {d : ℝ} (P : ARoom d) (q dr Ar : ℝ) (p : ℕ)
    (hdr : 0 < dr) (hAr : 0 < Ar) (F : smoothCompactFiniteSphereCore hO hD) (x : R3)
    (ht : (Tq dr Ar p q) x ∈ ParamRoom d) :
    finiteCoreSobolevLift hO hD (1/2 : ℝ)
        (nativeReferenceAdjointZeroCoefficient hO hD hF g hg L q dr Ar p hdr hAr F) x =
      RHalf q dr Ar p F x+Corr P q dr Ar p x
        (finiteCoreSobolevLift hO hD (3/2 : ℝ) F x) := by
  apply sphereSobolevInclusionL_injective (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  rw [map_add,genuine_reverse_half_negative_graph
    hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data P q dr Ar p F x ht]
  exact (native_adjoint_zero_negative_graph hO hD hF g hg L q dr Ar p hdr hAr F x).trans
    (raw_adjoint_zero_eq_genuine_reverse_add_correction
      hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data P q dr Ar p x ht _)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTZeroGenuineReverse

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTZeroGenuineReverse.raw_adjoint_zero_eq_genuine_reverse_add_correction
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTZeroGenuineReverse.genuine_reverse_half_negative_graph
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTZeroGenuineReverse.native_raw_adjoint_zero_half_eq_genuine_reverse_add_correction
