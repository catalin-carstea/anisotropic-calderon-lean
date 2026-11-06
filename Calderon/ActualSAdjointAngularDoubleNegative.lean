import Calderon.ActualHigherSAdjointFormation
import Calderon.ActualZHalfRealization

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Metric
open scoped BigOperators ContDiff InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualSAdjointAngularDoubleNegative
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFiniteHarmonicCore ActualHigherSFormation
  ActualGeneratorEPairedGainedEndpoints ActualReverseEHigherLift
  ActualCommonFirstWordQuadraticAdjoint ReferenceDensityBounds ConformalDepth

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "Tpar" => (ℝ × (R3 × ℝ)) × (R3 →L[ℝ] ℝ)
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete
@[instance_reducible] private def highNegativeNormed : NormedAddCommGroup (Hi →L[ℝ] Neg) := inferInstance
@[instance_reducible] private def highNegativeSpace : NormedSpace ℝ (Hi →L[ℝ] Neg) := inferInstance
attribute [local instance] highNegativeNormed highNegativeSpace
@[instance_reducible] private def halfNegativeNormed : NormedAddCommGroup (Half →L[ℝ] Neg) := inferInstance
@[instance_reducible] private def halfNegativeSpace : NormedSpace ℝ (Half →L[ℝ] Neg) := inferInstance
attribute [local instance] halfNegativeNormed halfNegativeSpace
@[instance_reducible] private def highHalfNormed : NormedAddCommGroup (Hi →L[ℝ] Half) := inferInstance
@[instance_reducible] private def highHalfSpace : NormedSpace ℝ (Hi →L[ℝ] Half) := inferInstance
attribute [local instance] highHalfNormed highHalfSpace

private lemma norm_angular_sum {X Y Z : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (r : ℝ) (Q : Fin 3 → Fin 3 → ℝ)
    (ah eh : Fin 3 → X →L[ℝ] Y) (al el : Fin 3 → Y →L[ℝ] Z) :
    ‖r • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • ((el j).comp (ah i)+(al j).comp (eh i)))‖ ≤
      |r| *(∑ i : Fin 3, ∑ j : Fin 3, |Q i j| *(‖el j‖*‖ah i‖+‖al j‖*‖eh i‖)) := by
  rw [norm_smul,Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg r)
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro i _
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro j _
  rw [norm_smul,Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg (Q i j))
  exact (norm_add_le _ _).trans (add_le_add
    (ContinuousLinearMap.opNorm_comp_le _ _) (ContinuousLinearMap.opNorm_comp_le _ _))

private lemma norm_double_sum {X Y Z : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (r : ℝ) (Q : Fin 3 → Fin 3 → ℝ)
    (eh : Fin 3 → X →L[ℝ] Y) (el : Fin 3 → Y →L[ℝ] Z) :
    ‖r • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • (el j).comp (eh i))‖ ≤
      |r| *(∑ i : Fin 3, ∑ j : Fin 3, |Q i j| *(‖el j‖*‖eh i‖)) := by
  rw [norm_smul,Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg r)
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro i _
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro j _
  rw [norm_smul,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (abs_nonneg (Q i j))

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)

local notation "CoeffRoom" => CoefficientGermRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "CRoom" => CommonFirstWordRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "eH" => reverseEHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "eL" => reverseELow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "aH" => loweringHigh hF hO hD
local notation "aL" => loweringLow hF hO hD
local notation "Tq" dr:max Ar:max p:max q:max => higherSParam L dr Ar p q
local notation "Uin" => higherSInput hO hD
local notation "VR" => reverseEHigherLift g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "LA" => ActualHigherSAngularAdjoint.loweringInput hF hO hD

/-- Whole ordered angular reverse as a genuine Hi-to-negative operator. -/
def angularAdjointNegative (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ) (x : R3) :
    Hi →L[ℝ] Neg :=
  referenceRadius dr Ar p L x • (∑ i : Fin 3, ∑ j : Fin 3,
    referenceDensityPrincipalFrameCoefficient g g2 L q x i j •
      ((eL j ((Tq dr Ar p q) x)).comp (aH i) +
        (aL j).comp (eH i ((Tq dr Ar p q) x))))

/-- Whole reversed-order quadratic reverse as a genuine Hi-to-negative operator. -/
def doubleAdjointNegative (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ) (x : R3) :
    Hi →L[ℝ] Neg :=
  (referenceRadius dr Ar p L x)^3 • (∑ i : Fin 3, ∑ j : Fin 3,
    referenceDensityPrincipalFrameCoefficient g g2 L q x i j •
      (eL j ((Tq dr Ar p q) x)).comp (eH i ((Tq dr Ar p q) x)))

local notation "AN" => angularAdjointNegative g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "DN" => doubleAdjointNegative g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

/-- Exact angular source dictionary on the caller's unchanged retained room. -/
theorem revAngularHalf_inclusion (hreg : FixedDirichletRegularity) (δ0 : ℝ)
    (W : CoeffRoom δ0) (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3)
    (hTx : (Tq dr Ar p q) x ∈ ParamRoom δ) :
    JL (ActualHigherSAngularAdjoint.revAngularHalf g L y0 Φ B ε C ρ H a w hData hg hcalc
      hF hO hD τ0 hreg δ0 W g2 dr Ar p q F x) = AN g2 dr Ar p q x (Uin F x) := by
  have hE (j : Fin 3) (v : Hi) :
      JL (eH j ((Tq dr Ar p q) x) v) = eL j ((Tq dr Ar p q) x) (IH v) :=
    Cm.rev.compat j _ hTx v
  have hV (i : Fin 3) : IH (VR hreg δ0 W dr Ar p q F i x) =
      eH i ((Tq dr Ar p q) x) (Uin F x) :=
    reverseEHigherLift_inclusion_of_graph g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W dr Ar p q F i x (Cm.rev.graph (Sum.inr ()) i _ hTx) (Cm.rev.compat i _ hTx)
  have hTerm (i j : Fin 3) :
      JL (eH j ((Tq dr Ar p q) x) (LA F i x) + aH j (VR hreg δ0 W dr Ar p q F i x)) =
        eL j ((Tq dr Ar p q) x) (aH i (Uin F x)) +
          aL j (eH i ((Tq dr Ar p q) x) (Uin F x)) := by
    have hOne := (hE j (LA F i x)).trans
      (congrArg (eL j ((Tq dr Ar p q) x))
        (ActualHigherSAngularAdjoint.loweringInput_inclusion hF hO hD F i x))
    have hTwo := (v017_inclusion_loweringHigh hF hO hD j (VR hreg δ0 W dr Ar p q F i x)).trans
      (congrArg (aL j) (hV i))
    exact (map_add JL _ _).trans (congrArg₂ (fun v z : Neg => v+z) hOne hTwo)
  simp only [ActualHigherSAngularAdjoint.revAngularHalf,angularAdjointNegative,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply,map_smul,map_sum]
  apply congrArg (fun z : Neg => referenceRadius dr Ar p L x • z)
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun z : Neg => referenceDensityPrincipalFrameCoefficient g g2 L q x i j • z)
    (hTerm i j)

/-- Exact quadratic source dictionary, preserving the reversed i,j operator order. -/
theorem revDoubleHalf_inclusion (hreg : FixedDirichletRegularity) (δ0 : ℝ)
    (W : CoeffRoom δ0) (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3)
    (hTx : (Tq dr Ar p q) x ∈ ParamRoom δ) :
    JL (revDoubleHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W g2 dr Ar p q F x) = DN g2 dr Ar p q x (Uin F x) := by
  have hV (i : Fin 3) : IH (VR hreg δ0 W dr Ar p q F i x) =
      eH i ((Tq dr Ar p q) x) (Uin F x) :=
    reverseEHigherLift_inclusion_of_graph g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W dr Ar p q F i x (Cm.rev.graph (Sum.inr ()) i _ hTx) (Cm.rev.compat i _ hTx)
  have hTerm (i j : Fin 3) :
      JL (eH j ((Tq dr Ar p q) x) (VR hreg δ0 W dr Ar p q F i x)) =
        eL j ((Tq dr Ar p q) x) (eH i ((Tq dr Ar p q) x) (Uin F x)) :=
    (Cm.rev.compat j _ hTx _).trans (congrArg (eL j ((Tq dr Ar p q) x)) (hV i))
  simp only [revDoubleHalf,doubleAdjointNegative,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply,map_smul,map_sum]
  apply congrArg (fun z : Neg => (referenceRadius dr Ar p L x)^3 • z)
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun z : Neg => referenceDensityPrincipalFrameCoefficient g g2 L q x i j • z)
    (hTerm i j)

/-- Literal actual operator budget, with both angular ordered summands. -/
def angularBudget (g2 : MatrixField) (q : ℝ) (x : R3) (t : Tpar) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3, |referenceDensityPrincipalFrameCoefficient g g2 L q x i j| *
    (‖eL j t‖*‖aH i‖ + ‖aL j‖*‖eH i t‖)

/-- Literal actual reversed quadratic operator budget. -/
def doubleBudget (g2 : MatrixField) (q : ℝ) (x : R3) (t : Tpar) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3, |referenceDensityPrincipalFrameCoefficient g g2 L q x i j| *
    (‖eL j t‖*‖eH i t‖)

local notation "BA" => angularBudget g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "BD" => doubleBudget g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

attribute [local irreducible] reverseEHigh reverseELow loweringHigh loweringLow
  referenceRadius referenceDensityPrincipalFrameCoefficient higherSParam

/-- Proved norm cap for the genuine full angular negative operator. -/
theorem norm_angularAdjointNegative_le (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ) (x : R3) :
    ‖AN g2 dr Ar p q x‖ ≤ |referenceRadius dr Ar p L x| * BA g2 q x ((Tq dr Ar p q) x) := by
  exact norm_angular_sum (X := Hi) (Y := Half) (Z := Neg) (referenceRadius dr Ar p L x)
    (referenceDensityPrincipalFrameCoefficient g g2 L q x)
    aH (fun i => eH i ((Tq dr Ar p q) x))
    aL (fun j => eL j ((Tq dr Ar p q) x))

/-- Proved norm cap for the genuine full reversed quadratic negative operator. -/
theorem norm_doubleAdjointNegative_le (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ) (x : R3) :
    ‖DN g2 dr Ar p q x‖ ≤ |(referenceRadius dr Ar p L x)^3| * BD g2 q x ((Tq dr Ar p q) x) := by
  exact norm_double_sum (X := Hi) (Y := Half) (Z := Neg) ((referenceRadius dr Ar p L x)^3)
    (referenceDensityPrincipalFrameCoefficient g g2 L q x)
    (fun i => eH i ((Tq dr Ar p q) x)) (fun j => eL j ((Tq dr Ar p q) x))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualSAdjointAngularDoubleNegative
