import Calderon.ActualHigherSZeroPhysicalGraph
import Calderon.ActualLowerUSLowerWordAdjoints

/-! Exact finite quadratic commutator telescope and half/three-half bound.
The generic bound is a reduction lemma; it introduces no new analytic premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Metric
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSFiniteQuadraticCommutator
open EnergyBridge ConnectionError SphereHarmonic ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualAngularHighDraft ActualAngularPiDraft ActualFullEGainedEndpoints ActualRetainedGeneratorMultiplierGains
  SmoothMetricFrame MovingFrameConnection ReferenceDensityBounds ConformalDepth ReferenceWeightedApproximation
  ActualHigherSZeroPhysicalGraph
  ActualFiniteHarmonicModel.ActualLowerUSLowerWordAdjoints

section FiniteReduction
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
local notation "FC" => smoothCompactFiniteSphereCore hO hD
private abbrev finiteWeightValue (s : ℝ) (F : FC) (x : R3) : SphereL2 :=
  (coreWeightOperator hO hD (SpectralWeightedGraph.besselWeight s) F).val x
local notation "W" s:max F:max x:max => finiteWeightValue hO hD s F x

/-- Q is allowed to have an arbitrary nonfinite physical SphereL2 output.
This exact identity is algebraic even before its linearity is established. -/
lemma finite_quadratic_zero_commutator_split
    (Q : FC → SphereL2) (A Astar B Bstar : Module.End ℝ FC) (F G : FC) (x : R3) :
    ⟪((Bstar*Astar) F).val x,Q G⟫_ℝ - ⟪F.val x,Q ((A*B) G)⟫_ℝ =
      (⟪(Bstar (Astar F)).val x,Q G⟫_ℝ - ⟪(Astar F).val x,Q (B G)⟫_ℝ) +
      (⟪(Astar F).val x,Q (B G)⟫_ℝ - ⟪F.val x,Q (A (B G))⟫_ℝ) := by
  simp only [Module.End.mul_apply]
  ring

/-- Both finite orientations of the actual first-generator/Q bound suffice.
Only the genuine finite pretests Astar F and B G occur. -/
lemma finite_quadratic_zero_commutator_bound
    (Q : FC → SphereL2) (A Astar B Bstar : Module.End ℝ FC)
    (CA CB M : ℝ) (x : R3) (hM : 0 ≤ M)
    (hA : HasCoreAngularFirstOrderBounds hO hD A Astar CA x)
    (hB : HasCoreAngularFirstOrderBounds hO hD B Bstar CB x)
    (hBComm : ∀ U V : FC,
      |⟪(Bstar U).val x,Q V⟫_ℝ - ⟪U.val x,Q (B V)⟫_ℝ| ≤
        M*‖W (1/2 : ℝ) U x‖*‖W (3/2 : ℝ) V x‖)
    (hAComm : ∀ U V : FC,
      |⟪(Astar U).val x,Q V⟫_ℝ - ⟪U.val x,Q (A V)⟫_ℝ| ≤
        M*‖W (3/2 : ℝ) U x‖*‖W (1/2 : ℝ) V x‖)
    (F G : FC) :
    |⟪((Bstar*Astar) F).val x,Q G⟫_ℝ - ⟪F.val x,Q ((A*B) G)⟫_ℝ| ≤
      ((CA+CB)*M)*‖W (3/2 : ℝ) F x‖*‖W (3/2 : ℝ) G x‖ := by
  have h1 := (hBComm (Astar F) G).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hA.2.2.2.2 F) hM) (norm_nonneg _))
  have h2 := (hAComm F (B G)).trans
    (mul_le_mul_of_nonneg_left (hB.2.2.2.1 G) (mul_nonneg hM (norm_nonneg _)))
  rw [finite_quadratic_zero_commutator_split hO hD]
  calc
    _ ≤ |⟪(Bstar (Astar F)).val x,Q G⟫_ℝ - ⟪(Astar F).val x,Q (B G)⟫_ℝ| +
        |⟪(Astar F).val x,Q (B G)⟫_ℝ - ⟪F.val x,Q (A (B G))⟫_ℝ| := abs_add_le _ _
    _ ≤ M*(CA*‖W (3/2 : ℝ) F x‖)*‖W (3/2 : ℝ) G x‖ +
        M*‖W (3/2 : ℝ) F x‖*(CB*‖W (3/2 : ℝ) G x‖) := add_le_add h1 h2
    _ = _ := by ring
end FiniteReduction

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)
local notation "CoeffRoom" => CoefficientGermRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "CRoom" => ActualCommonFirstWordQuadraticAdjoint.CommonFirstWordRoom
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "Tq" δr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L δr Ar p q
local notation "CZc" => ActualHigherSZeroCoefficientJets.canonicalZeroCoefficient
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "UF" => ActualHigherSFormation.higherSInput hO hD


/-- The single primitive commutator expression used by both estimates.
The angular adjoint is genuine and Qout is the full native physical output. -/
def lowerGeneratorZeroCommutatorDensity
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (i : LowerCoreAngularGeneratorIndex)
    (U V : smoothCompactFiniteSphereCore hO hD) (x : R3) : ℝ :=
  ⟪(lowerCoreAngularGeneratorAdjoint hO hD hF i U).val x,
    nativeZeroOut g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W g2 dr Ar p hdr hAr q V x⟫_ℝ -
  ⟪U.val x,nativeZeroOut g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W g2 dr Ar p hdr hAr q (lowerCoreAngularGenerator hO hD hF i V) x⟫_ℝ

/-- The quadratic word's exact physical commutator splits into the two
primitive densities at genuine finite inputs. -/
theorem lowerQuadraticWord_zero_commutator_split
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (ij : LowerCoreAngularGeneratorIndex × LowerCoreAngularGeneratorIndex)
    (F G : smoothCompactFiniteSphereCore hO hD) (x : R3) :
  ⟪(lowerQuadraticWordAdjoint hO hD hF ij F).val x,
    nativeZeroOut g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W g2 dr Ar p hdr hAr q G x⟫_ℝ -
  ⟪F.val x,nativeZeroOut g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W g2 dr Ar p hdr hAr q (lowerQuadraticWord hO hD hF ij G) x⟫_ℝ =
  lowerGeneratorZeroCommutatorDensity g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W g2 dr Ar p hdr hAr q ij.2
      (lowerCoreAngularGeneratorAdjoint hO hD hF ij.1 F) G x +
  lowerGeneratorZeroCommutatorDensity g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W g2 dr Ar p hdr hAr q ij.1 F
      (lowerCoreAngularGenerator hO hD hF ij.2 G) x := by
  unfold lowerQuadraticWordAdjoint lowerQuadraticWord lowerGeneratorZeroCommutatorDensity
  simp only [Module.End.mul_apply]
  ring

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSFiniteQuadraticCommutator
