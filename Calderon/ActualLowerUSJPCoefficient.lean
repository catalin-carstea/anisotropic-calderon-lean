import Calderon.ActualLowerUSJPWords
import Calderon.ActualLowerUSJPPresentation
import Calderon.ActualHigherSCoordinateWeightBounds

/-! Author-support GPT-6.1 Sol. Before-code ../gained-jp-upfront-v001.md.
Actual ordered coordinate-weight contraction of the gained J-word/E maps.
No compiler by author. Helper caps are obtained internally by the final producer. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Metric
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSJPCoefficient
open EnergyBridge ConnectionError SphereHarmonic ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualFullEGainedAssembly ActualFullEGainedEndpoints ActualAngularHighDraft ActualAngularPiDraft
  ActualRetainedGeneratorMultiplierGains ActualGeneratorEPairedGainedEndpoints ActualMixedAngularPairedGains
  ActualLowerUSSecondRow ActualLowerUSFirstAngularGainPair ActualHigherSPhysicalPairing
  ReferenceDensityBounds ConformalDepth ReferenceWeightedApproximation NormalizedPrincipalMetric
  ActualLowerUSJPWords ActualLowerUSFirstOutput ActualLowerUSJPPresentation
  ActualHigherSLeadingBracketGain ActualHigherSCoordinateWeightBounds
  ActualFiniteHarmonicModel.ActualLowerUSLowerWordAdjoints
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "PP" => sphereSobolevDualPairing (1/2 : ℝ)
local notation "Tpar" => (ℝ × (R3 × ℝ)) × (R3 →L[ℝ] ℝ)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)
  (Room : ReferenceGaugeNormalReciprocalRoom g L Φ a
    (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ)))
  (hreg : FixedDirichletRegularity)
  (data : FullEPhysicalEndpointRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg)
local notation "MRoom" => MixedAngularPhysicalEndpointRoom hF hO hD hcalc τ0
  g L y0 Φ B ε C ρ H a w hData hg hreg data.δ0 data.germs
local notation "GRoom" δ:max => GeneratorEndpointRoom
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg data.δ0 data.germs δ
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "EH" => canonicalHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "EL" => canonicalLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

local notation "Tq" dr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L dr Ar p q
local notation "Pout" g2:max dr:max Ar:max p:max q:max =>
  nativeFirstOut g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q
local notation "QW" => quadraticEWord g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "GL" => firstAngularGain g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "GH" => firstAngularGainHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "GS" => firstAngularGainSharpHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "GSL" => firstAngularGainSharpLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data

/-- The genuine r² and both ordered principal coordinate weights are retained. -/
def quadraticPWordCoefficient (adjoint : Bool) (mixed : MRoom) (δ : ℝ) (gen : GRoom δ)
    (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ) (j : Fin 3) (x : R3)
    (ij : LowerCoreAngularGeneratorIndex × LowerCoreAngularGeneratorIndex) : Hi →L[ℝ] Neg :=
  (referenceRadius dr Ar p L x)^2 • ∑ k : Fin 3,
    firstCoordinateWeight g g2 L j k ((Tq dr Ar p q) x) •
      QW adjoint mixed δ gen k ((Tq dr Ar p q) x) ij
local notation "PW" => quadraticPWordCoefficient
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data

lemma quadraticPWord_pairing (mixed : MRoom) (δ : ℝ) (gen : GRoom δ)
    (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ) (j : Fin 3) (x : R3)
    (htG : (Tq dr Ar p q) x ∈ ParamRoom δ) (htM : (Tq dr Ar p q) x ∈ ParamRoom mixed.δ)
    (ij : LowerCoreAngularGeneratorIndex × LowerCoreAngularGeneratorIndex) (u v : Hi) :
    PP (IH u) (PW false mixed δ gen g2 dr Ar p q j x ij v) =
      PP (IH v) (PW true mixed δ gen g2 dr Ar p q j x ij u) := by
  simp only [quadraticPWordCoefficient,smul_apply,sum_apply,sphereSobolevDualPairing,
    real_inner_smul_right,inner_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  exact quadraticEWord_pairing g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    Room hreg data mixed δ gen k _ htG htM ij u v

lemma quadraticPWord_physical_graph (mixed : MRoom) (δ : ℝ) (gen : GRoom δ)
    (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ) (j : Fin 3) (x : R3)
    (htG : (Tq dr Ar p q) x ∈ ParamRoom δ) (htM : (Tq dr Ar p q) x ∈ ParamRoom mixed.δ)
    (htD : (Tq dr Ar p q) x ∈ ParamRoom data.δ)
    (ij : LowerCoreAngularGeneratorIndex × LowerCoreAngularGeneratorIndex)
    (U V : smoothCompactFiniteSphereCore hO hD) :
    ⟪(lowerQuadraticWordAdjoint hO hD hF ij U).val x,(Pout g2 dr Ar p q) j V x⟫_ℝ -
      ⟪U.val x,(Pout g2 dr Ar p q) j (lowerQuadraticWord hO hD hF ij V) x⟫_ℝ =
    PP (finiteCoreSobolevLift hO hD (1/2 : ℝ) U x)
      (PW false mixed δ gen g2 dr Ar p q j x ij (finiteCoreSobolevLift hO hD (3/2 : ℝ) V x)) := by
  rw [nativeFirstOut_contracted,nativeFirstOut_contracted]
  simp only [real_inner_smul_right,inner_sum]
  rw [← mul_sub,← Finset.sum_sub_distrib]
  simp only [← mul_sub]
  simp_rw [quadraticEWord_physical_graph g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    Room hreg data mixed δ gen _ _ htG htM htD ij U V x]
  simp only [quadraticPWordCoefficient,smul_apply,sum_apply,sphereSobolevDualPairing,
    real_inner_smul_right,inner_sum]

lemma norm_quadraticPWord_le (adjoint : Bool) (mixed : MRoom) (δ : ℝ) (gen : GRoom δ)
    (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ) (j : Fin 3) (x : R3)
    (M MW : ℝ) (hM : 0 ≤ M) (hMW : 0 ≤ MW)
    (hGain : ∀ k : Fin 3, ∀ v : FirstAngularIndex,
      ‖GL mixed δ gen k ((Tq dr Ar p q) x) v‖ ≤ M ∧
      ‖GH mixed k ((Tq dr Ar p q) x) v‖ ≤ M ∧
      ‖GS k ((Tq dr Ar p q) x) v‖ ≤ M ∧
      ‖GSL mixed δ gen k ((Tq dr Ar p q) x) v‖ ≤ M)
    (hWeight : ∀ k : Fin 3, |firstCoordinateWeight g g2 L j k ((Tq dr Ar p q) x)| ≤ MW)
    (ij : LowerCoreAngularGeneratorIndex × LowerCoreAngularGeneratorIndex) :
    ‖PW adjoint mixed δ gen g2 dr Ar p q j x ij‖ ≤
      (6*MW*jpOrdinaryGeneratorBudget hF hO hD*M)*(referenceRadius dr Ar p L x)^2 := by
  let R := referenceRadius dr Ar p L x
  let T := 2*jpOrdinaryGeneratorBudget hF hO hD*M
  let A : Fin 3 → Hi →L[ℝ] Neg := fun k =>
    firstCoordinateWeight g g2 L j k ((Tq dr Ar p q) x) •
      QW adjoint mixed δ gen k ((Tq dr Ar p q) x) ij
  have hA (k : Fin 3) : ‖A k‖ ≤ MW*T := by
    dsimp only [A]
    calc
      _ ≤ ‖firstCoordinateWeight g g2 L j k ((Tq dr Ar p q) x)‖ *
          ‖QW adjoint mixed δ gen k ((Tq dr Ar p q) x) ij‖ :=
        ContinuousLinearMap.opNorm_smul_le _ _
      _ ≤ MW*T := by
        rw [Real.norm_eq_abs]
        exact mul_le_mul (hWeight k)
          (norm_quadraticEWord_le g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
            Room hreg data adjoint mixed δ gen k _ M hM (hGain k) ij)
          (norm_nonneg (QW adjoint mixed δ gen k ((Tq dr Ar p q) x) ij)) hMW
  have hSum : ‖∑ k : Fin 3, A k‖ ≤ 3*MW*T := by
    calc
      _ ≤ ∑ k : Fin 3, ‖A k‖ := norm_sum_le Finset.univ A
      _ ≤ ∑ k : Fin 3, MW*T := Finset.sum_le_sum (fun k _ => hA k)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring
  change ‖R^2 • ∑ k : Fin 3, A k‖ ≤ _
  calc
    _ ≤ ‖R^2‖ * ‖∑ k : Fin 3, A k‖ := ContinuousLinearMap.opNorm_smul_le _ _
    _ ≤ ‖R^2‖ * (3*MW*T) := mul_le_mul_of_nonneg_left hSum (norm_nonneg _)
    _ = _ := by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg R)]
      dsimp only [T,R]
      ring

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSJPCoefficient
