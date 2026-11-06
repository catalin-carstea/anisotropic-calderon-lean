import Calderon.ActualRaisingECoordinateRegularity
import Calderon.ActualHigherSCoefficientBounds
import Calderon.ActualHighAdjointSmoothMultiplierBoundaryCommutator
import Calderon.LocalSmoothSignedTaylorRemainder
import Calderon.ActualFinitePhysicalDomainCommonRoom
import Calderon.ActualHigherSFormation
import Calderon.ActualHigherSAngularAdjoint
import Calderon.ActualCommonFirstWordQuadraticAdjoint
import Calderon.ActualGeneratorEHighGainedGraph
import Calderon.ActualGeneratorEPairedGainedEndpoints
import Calderon.ActualPiJacobiRadialGainedRows
import Calderon.ActualAngularHighDraft
import Calderon.SphereSobolevAngularRaisingSingle
import Calderon.ActualFiniteHarmonicModelRaisingCommute

/-! Opus v079 author-only source, 30 October 2026. UNCOMPILED until Root checks.
Before-source mathematics: MATHEMATICS.md (same output directory). Repairs v078 internally.
* `hRepH/hRepL` discharged by `rfl` (definition of raisingHigh/raisingLow);
* raising symmetry proved from native singles + `harmonicDerivativeAdjoint_composition_commute`
  + partial sums (method of native `gainedHigh_graph`);
* uniform cap CC of `C_A` on one retained compact room, before g2/profile/F/cutoff, from
  continuity of every actual factor. Root supplies actual high-coordinate Taylor regularity
  on its native retained high-invertibility room; no continuity premise remains in the cap/final theorems;
* literal original `higherSAngularHalf` principal/error identity and `9 CQ CC R ‖U‖` bound.
NOT proved: S-Sdag, double-E, weighted integral, cofinal uniformity, coercivity, Main. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualRaisingEHighGainedEndpoints
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualJacobiAngularGainedRows ActualPiJacobiRadialGainedRows
  ActualRetainedGeneratorMultiplierGains ActualGeneratorRadialGainedRows
  ActualCanonicalGeneratorAngularGainedRows NativeThreeHalfCoefficientMultiplier
  NativeCoefficientBoundaryMultiplier NativeOrderOneCoefficientMultiplier
  SmoothMetricFrame MovingFrameConnection ActualGeneratorEHighGainedGraph
  SphereHilbertDecomposition SpectralCoreRegularity SpectralWeightedGraph HarmonicDerivativeOperator
  ActualFiniteHarmonicCore ReferenceDensityBounds ConformalDepth
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "Pphys" => ℝ × (R3 × ℝ)
local notation "Tpar" => Pphys × (R3 →L[ℝ] ℝ)
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete
@[instance_reducible] private def raisingGainNormed : NormedAddCommGroup (Hi →L[ℝ] Half) := inferInstance
@[instance_reducible] private def raisingGainModule : NormedSpace ℝ (Hi →L[ℝ] Half) := inferInstance
@[instance_reducible] private def raisingHighNormed : NormedAddCommGroup (Hi →L[ℝ] Hi) := inferInstance
@[instance_reducible] private def raisingHighModule : NormedSpace ℝ (Hi →L[ℝ] Hi) := inferInstance
attribute [local instance] raisingGainNormed raisingGainModule raisingHighNormed raisingHighModule


variable (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace)
local notation "CoeffRoom" => CoefficientGermRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "EH" => canonicalHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "EL" => canonicalLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ZH" => zeroCorrectionHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ZL" => zeroCorrectionHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "NH" => nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
local notation "NL" => nativeHalfCoefficientMulL hcalc hF hO hD τ0
local notation "Th" => adjointHighRemainder hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "Tl" => adjointHalfRemainder hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "Ω" => referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "PiH" => referencePiThreeHalfMultiplier g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "PiL" => referencePiHalfMultiplier g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "NJ3" => referenceJacobiBoundaryThreeHalfCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData
local notation "NJ2" => referenceJacobiBoundaryCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData
local notation "QW" => retainedJets g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "GH" => retainedGeneratorHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "AH" => raisingHigh hF hO hD
local notation "AL" => raisingLow hF hO hD
local notation "Mh" j:max => sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ) (EuclideanSpace.single j (1 : ℝ))
local notation "Ml" j:max => sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ) (EuclideanSpace.single j (1 : ℝ))
local notation "Mn" j:max => sphereSobolevLinearCoordinateMulL hF hO hD (-(1/2 : ℝ)) (EuclideanSpace.single j (1 : ℝ))
local notation "Rh" j:max i:max => sphereSobolevRotationL (3/2 : ℝ) j i
local notation "Rl" j:max i:max => sphereSobolevRotationL (1/2 : ℝ) j i
local notation "BH" => (sphereSobolevShiftedDegreeL (3/2 : ℝ) : Hi →L[ℝ] Half)
local notation "BL" => (sphereSobolevShiftedDegreeL (1/2 : ℝ) : Half →L[ℝ] Neg)
local notation "CRoom" => ActualCommonFirstWordQuadraticAdjoint.CommonFirstWordRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "TT" δr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L δr Ar p q
local notation "UF" => ActualHigherSFormation.higherSInput hO hD
local notation "UAF" => ActualHigherSFormation.higherSRaisingInput hF hO hD
local notation "VFL" => ActualHigherSFormation.higherSLift hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
local notation "TS" F0:max => tsupport (F0 : R3 → SphereL2)

local notation "XG" => coordinateAdjointHighGain hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
attribute [local irreducible] raisingHigh raisingLow sphereSobolevInclusionL
  sphereSobolevAngularCoordinateTransposeL sphereSobolevRotationL sphereSobolevShiftedDegreeL
  sphereSobolevLinearCoordinateMulL sphereSobolevSingleL sphereSobolevCoefficientL
  referenceHighAdjointSmoothMultiplierBoundaryCommutatorFamily

/-- `K_i = Σ_j (Rot_ji X_j - CrT_ji M_j) - B X_i + CdT M_i`. -/
def radialRaisingHigh (hreg : FixedDirichletRegularity) (i : Fin 3) (p : Pphys) : Hi →L[ℝ] Half :=
  (∑ j : Fin 3, ((Rh j i).comp (XG j p) -
    (adjointRotationGain hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData j i p).comp (Mh j))) -
  (BH).comp (XG i p) +
  (adjointDegreeGain hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg p).comp (Mh i)

/-- `[A_i, N_c]` at Hi: `-Σ_j GH(rot j i) c M_j + GH(deg) c M_i`. -/
def raisingMultiplierHigh (δ0 : ℝ) (W : CoeffRoom δ0) (i : Fin 3) (c : RetainedCoefficient)
    (t : Tpar) : Hi →L[ℝ] Hi :=
  (-∑ j : Fin 3, (GH δ0 W (Sum.inl (j,i)) c t).comp (Mh j)) + (GH δ0 W (Sum.inr ()) c t).comp (Mh i)

/-- The actual gained raising/E high family `C_Aij`. -/
def raisingEHigh (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (i j : Fin 3) (t : Tpar) : Hi →L[ℝ] Half :=
  (radialRaisingHigh hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 hreg i t.1).comp (PiH j t) +
    (Th t.1).comp (raisingMultiplierHigh hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 δ0 W i
      (Sum.inl j) t) +
    (∑ m : Fin 3, (AH m).comp (raisingMultiplierHigh hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      δ0 W i (Sum.inr (j,m)) t)) +
    ((AH i).comp (ZH j t.1) - (ZL j t.1).comp (AH i))
local notation "CAE" => raisingEHigh hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0

lemma coordinate_native_high_comm (Q : SmoothCoefficientJets 3) (j : Fin 3) (x : Hi) :
    (Mh j) (NH Q x) = NH Q ((Mh j) x) := by
  apply sphereSobolevInclusionL_injective (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  have hM (y : Hi) := sphereSobolevInclusionL_linearCoordinateMul hF hO hD (3/2 : ℝ) (1/2 : ℝ)
    (by norm_num) (EuclideanSpace.single j (1 : ℝ)) y
  have hN (u : Hi) := v017_native_high_half hcalc hF hO hD τ0 Q u
  calc
    IH ((Mh j) (NH Q x)) = (Ml j) (IH (NH Q x)) := hM _
    _ = (Ml j) (NL (smoothMultiplierLowerJets Q) (IH x)) := congrArg (Ml j) (hN x)
    _ = NL (smoothMultiplierLowerJets Q) ((Ml j) (IH x)) := by
      simpa only [coordinateJets_half hcalc hF hO hD τ0 j] using
        nativeHalfCoefficientMulL_lowerJets_comm_apply hcalc hF hO hD τ0 (coordinateJets j) Q (IH x)
    _ = NL (smoothMultiplierLowerJets Q) (IH ((Mh j) x)) := congrArg (NL (smoothMultiplierLowerJets Q)) (hM x).symm
    _ = IH (NH Q ((Mh j) x)) := (hN _).symm

lemma coordinateAdjointHighGain_graph (hreg : FixedDirichletRegularity)
    (G : Fin 3 → Pphys → Half →L[ℝ] Half) (j : Fin 3) (p : Pphys)
    (hSeg : ∀ θ ∈ Icc (0 : ℝ) 1, (p.1,(p.2.1,θ*p.2.2)) ∈ Ω)
    (hRestrict : ∀ u : Hi, G j p (IH u) = IH (XG j p u))
    (hLow : ∀ v : Half, JL (G j p v) = Tl p ((Ml j) v) - (Mn j) (Tl p v)) (u : Hi) :
    IH (XG j p u) = Th p ((Mh j) u) - (Ml j) (Th p u) := by
  have hT (x : Hi) : JL (Th p x) = Tl p (IH x) :=
    v016_actual_Th_compat hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg p hSeg x
  have hM := sphereSobolevInclusionL_linearCoordinateMul hF hO hD (3/2 : ℝ) (1/2 : ℝ)
    (by norm_num) (EuclideanSpace.single j (1 : ℝ)) u
  have hM' := sphereSobolevInclusionL_linearCoordinateMul hF hO hD (1/2 : ℝ) (-(1/2 : ℝ))
    (by norm_num) (EuclideanSpace.single j (1 : ℝ)) (Th p u)
  apply sphereSobolevInclusionL_injective (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  calc
    JL (IH (XG j p u)) = JL (G j p (IH u)) := congrArg JL (hRestrict u).symm
    _ = Tl p ((Ml j) (IH u)) - (Mn j) (Tl p (IH u)) := hLow _
    _ = Tl p (IH ((Mh j) u)) - (Mn j) (JL (Th p u)) :=
      congrArg₂ (fun x y : Neg => x-y) (congrArg (Tl p) hM.symm) (congrArg (Mn j) (hT u).symm)
    _ = JL (Th p ((Mh j) u)) - JL ((Ml j) (Th p u)) :=
      congrArg₂ (fun x y : Neg => x-y) (hT _).symm hM'.symm
    _ = JL (Th p ((Mh j) u) - (Ml j) (Th p u)) := (map_sub JL _ _).symm

attribute [local irreducible] canonicalHigh canonicalLow adjointHighRemainder adjointHalfRemainder
  nativeThreeHalfCoefficientMulL nativeHalfCoefficientMulL referencePiThreeHalfMultiplier
  referencePiHalfMultiplier referenceJacobiBoundaryThreeHalfCoefficientFamily
  referenceJacobiBoundaryCoefficientFamily retainedGeneratorHigh retainedJets
  zeroCorrectionHigh zeroCorrectionHalf adjointRotationGain adjointDegreeGain
  radialRaisingHigh raisingMultiplierHigh raisingEHigh

/-- Root: atomic actual radial/raising graph, retaining every coordinate word. -/
lemma radialRaisingHigh_graph (hreg : FixedDirichletRegularity)
    (G : Fin 3 → Pphys → Half →L[ℝ] Half) (i : Fin 3) (p : Pphys)
    (hSeg : ∀ θ ∈ Icc (0 : ℝ) 1, (p.1,(p.2.1,θ*p.2.2)) ∈ Ω)
    (hGG : ∀ k : Fin 3, (∀ x : Hi, G k p (IH x) = IH (XG k p x)) ∧
      (∀ x : Half, JL (G k p x) = Tl p ((Ml k) x) - (Mn k) (Tl p x)))
    (x : Hi) : JL (radialRaisingHigh hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 hreg i p x) =
      AL i (Th p x) - Tl p (AH i x) := by
  have hX (k : Fin 3) (u : Hi) := coordinateAdjointHighGain_graph hF hO hD g L y0 Φ B ε C ρ H a w hData
    hg hcalc τ0 hreg G k p hSeg (hGG k).1 (hGG k).2 u
  have hRaw := radialRaising_cancel IH JL (Th p) (Tl p) (fun k => Rh k i) (fun k => Rl k i) BH BL
      (fun k => Mh k) (fun k => Ml k)
      (fun k => adjointRotationGain hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData k i p)
      (adjointDegreeGain hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg p)
      (fun k => XG k p) i
      (fun k y => congrArg (fun A : Hi →L[ℝ] Neg => A y)
        (sphereSobolevRotationL_threehalf_half_compatibility k i))
      (fun y => congrArg (fun A : Hi →L[ℝ] Neg => A y) sphereSobolevShiftedDegree_high_half_compatibility)
      hX
      (fun k y => by simpa only [adjointRotationGain,adjointHighRemainder,adjointHalfRemainder] using
        (referenceAdjointHighAngleSecondRemainder_completed_rotation_graph
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg k i p.1 p.2.1 p.2.2 hSeg y).symm)
      (fun y => by simpa only [adjointDegreeGain,adjointHighRemainder,adjointHalfRemainder] using
        (RawAdjointDegreeGainDraft.gainedHighSecondRemainder_signed_adjoint_degree_graph
          g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 p.1 p.2.1 p.2.2 hSeg y)) x
  simpa only [radialRaisingHigh,raisingHigh,raisingLow] using hRaw

/-- Root: atomic actual raising/multiplier graph. -/
lemma raisingMultiplierHigh_graph (δ0 : ℝ) (W : CoeffRoom δ0) (i : Fin 3)
    (c : RetainedCoefficient) (t : Tpar)
    (hRot : ∀ k : Fin 3, ∀ x : Hi,
      IH (GH δ0 W (Sum.inl (k,i)) c t x) =
        (Rh k i) (NH (QW δ0 W c t) x) - NL (smoothMultiplierLowerJets (QW δ0 W c t)) ((Rh k i) x))
    (hDeg : ∀ x : Hi, IH (GH δ0 W (Sum.inr ()) c t x) =
      BH (NH (QW δ0 W c t) x) - NL (smoothMultiplierLowerJets (QW δ0 W c t)) (BH x))
    (x : Hi) : IH (raisingMultiplierHigh hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 δ0 W i c t x) =
      AH i (NH (QW δ0 W c t) x) - NL (smoothMultiplierLowerJets (QW δ0 W c t)) (AH i x) := by
  have hRaw := raisingMultiplier_cancel IH (fun k => Rh k i) BH (fun k => Mh k) (NH (QW δ0 W c t))
      (NL (smoothMultiplierLowerJets (QW δ0 W c t)))
      (fun k => GH δ0 W (Sum.inl (k,i)) c t) (GH δ0 W (Sum.inr ()) c t) i hRot hDeg
      (fun k y => coordinate_native_high_comm hF hO hD hcalc τ0 (QW δ0 W c t) k y) x
  simpa only [raisingMultiplierHigh,raisingHigh] using hRaw

/-- Root: actual retained-germ graph assembly at a fixed point. -/
lemma raisingEHigh_graph_of_words (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (i j : Fin 3) (t : Tpar) (ht0 : t ∈ ParamRoom δ0)
    (hSeg : ∀ θ ∈ Icc (0 : ℝ) 1, (t.1.1,(t.1.2.1,θ*t.1.2.2)) ∈ Ω)
    (hK : ∀ x : Hi, JL (radialRaisingHigh hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 hreg i t.1 x) =
      AL i (Th t.1 x) - Tl t.1 (AH i x))
    (hM : ∀ c : RetainedCoefficient, ∀ x : Hi,
      IH (raisingMultiplierHigh hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 δ0 W i c t x) =
        AH i (NH (QW δ0 W c t) x) - NL (smoothMultiplierLowerJets (QW δ0 W c t)) (AH i x))
    (u : Hi) : JL (CAE hreg δ0 W i j t u) = AL i (EH j t u) - EL j t (AH i u) := by
  have hT (x : Hi) : JL (Th t.1 x) = Tl t.1 (IH x) :=
    v016_actual_Th_compat hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg t.1 hSeg x
  have hA (m : Fin 3) (x : Hi) : JL (AH m x) = AL m (IH x) := v017_inclusion_raisingHigh hF hO hD m x
  have hSym : ∀ i m : Fin 3, ∀ v : Hi, AL m (AH i v) = AL i (AH m v) :=
    fun i m v => raisingLow_comp_raisingHigh_symm hF hO hD i m v
  have hPi := (W.piGerm j t ht0).self_of_nhds
  have hGp (x : Hi) := hM (Sum.inl j) x
  have hGn (m : Fin 3) (x : Hi) := hM (Sum.inr (j,m)) x
  simp only [retainedJets,piJets,jacobiJets,hPi.1,hPi.2.1] at hGp
  have hN (m : Fin 3) := (W.jacobiGerm j m t.1 ht0.1).self_of_nhds
  have hGn' (m : Fin 3) (x : Hi) :
      IH (raisingMultiplierHigh hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 δ0 W i
        (Sum.inr (j,m)) t x) = AH i (NH (NJ3 j m t.1) x) - NL (NJ2 j m t.1) (AH i x) := by
    simpa only [retainedJets,jacobiJets,(hN m).1,(hN m).2.1] using hGn m x
  have hMain := raisingE_assembly IH JL (Th t.1) (Tl t.1) (PiH j t) (PiL j t) AH AL
    (fun m => NH (NJ3 j m t.1)) (fun m => NL (NJ2 j m t.1)) (ZH j t.1) (ZL j t.1)
    (radialRaisingHigh hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 hreg i t.1)
    (raisingMultiplierHigh hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 δ0 W i (Sum.inl j) t)
    (fun m => raisingMultiplierHigh hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 δ0 W i
      (Sum.inr (j,m)) t) i hK hGp hGn' (fun m x => hSym i m x) hA hT u
  simpa only [raisingEHigh,canonicalHigh,canonicalLow] using hMain

/-! ## 3. Actual graph on one retained room — NO representation/symmetry premise. -/
lemma exists_raisingE_graph_on_given_rooms (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (hδ0 : 0 < δ0) (W : CoeffRoom δ0)
    (dA dU : ℝ) (hdA : 0 < dA) (hdAρ : dA ≤ ρ) (hdU : 0 < dU)
    (hRoomA : commonRoom y0 ρ dA ⊆ Ω)
    (G : Fin 3 → Pphys → Half →L[ℝ] Half)
    (hGG : ∀ k : Fin 3, ∀ p ∈ commonRoom y0 ρ dA,
      (∀ u : Hi, G k p (IH u) = IH (XG k p u)) ∧
      (∀ v : Half, JL (G k p v) = Tl p ((Ml k) v) - (Mn k) (Tl p v)))
    (hUG : ∀ V : Generator, ∀ c : RetainedCoefficient, ∀ t ∈ ParamRoom dU, ∀ x : Hi,
      IH (GH δ0 W V c t x) = generatorHigh V (NH (QW δ0 W c t) x) -
        NL (smoothMultiplierLowerJets (QW δ0 W c t)) (generatorHigh V x)) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ0 ∧ δ ≤ ρ ∧ ∀ i j : Fin 3, ∀ t ∈ ParamRoom δ, ∀ u : Hi,
      JL (CAE hreg δ0 W i j t u) = AL i (EH j t u) - EL j t (AH i u) := by
  let δ := min δ0 (min dA dU)
  have hδ : 0 < δ := lt_min hδ0 (lt_min hdA hdU)
  have hδA : δ ≤ dA := (min_le_right _ _).trans (min_le_left _ _)
  have hδU : δ ≤ dU := (min_le_right _ _).trans (min_le_right _ _)
  have hSub0 := commonRoom_mono y0 ρ (show δ ≤ δ0 from min_le_left _ _)
  have hSubA := commonRoom_mono y0 ρ hδA
  have hSubU := commonRoom_mono y0 ρ hδU
  refine ⟨δ,hδ,min_le_left _ _,hδA.trans hdAρ,?_⟩
  intro i j t ht u
  have hSeg := segment_of_mem_commonRoom hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hRoomA t.1
    (hSubA ht.1)
  have hK (x : Hi) := radialRaisingHigh_graph hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
    hreg G i t.1 hSeg (fun k => hGG k t.1 (hSubA ht.1)) x
  have hM (c : RetainedCoefficient) (x : Hi) := raisingMultiplierHigh_graph
    hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 δ0 W i c t
    (fun k y => by simpa only [generatorHigh] using hUG (Sum.inl (k,i)) c t ⟨hSubU ht.1,ht.2⟩ y)
    (fun y => by simpa only [generatorHigh] using hUG (Sum.inr ()) c t ⟨hSubU ht.1,ht.2⟩ y) x
  exact raisingEHigh_graph_of_words hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
    hreg δ0 W i j t ⟨hSub0 ht.1,ht.2⟩ hSeg hK hM u


/-- Root: discard unused fields while all proposition payloads remain abstract. -/
private lemma keep_middle_graph {D G : Type*} {A B C : D → Prop} {P Q S : D → G → Prop}
    (h : ∃ d : D, A d ∧ B d ∧ C d ∧ ∃ g : G, P d g ∧ Q d g ∧ S d g) :
    ∃ d : D, A d ∧ B d ∧ C d ∧ ∃ g : G, Q d g := by
  rcases h with ⟨d,ha,hb,hc,g,_hp,hq,_hs⟩
  exact ⟨d,ha,hb,hc,g,hq⟩

/-- Root: retain exactly the native coordinate graph room, omitting unused caps. -/
lemma exists_raising_coordinate_graph_room (hreg : FixedDirichletRegularity)
    (hKernel : UnitBallValueTraceKernel τ0) :
    ∃ dA : ℝ, 0 < dA ∧ dA ≤ ρ ∧ commonRoom y0 ρ dA ⊆ Ω ∧
      ∃ G : Fin 3 → Pphys → Half →L[ℝ] Half,
      ∀ k : Fin 3, ∀ p ∈ commonRoom y0 ρ dA,
        (∀ u : Hi, G k p (IH u) = IH (XG k p u)) ∧
        (∀ v : Half, JL (G k p v) = Tl p ((Ml k) v) - (Mn k) (Tl p v)) := by
  have hNative := exists_reference_commonRadius_loweringAngularHigh_graph_caps
    hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg hg hKernel
  exact keep_middle_graph hNative

/-- Root: retain exactly the high generator/multiplier graph on the same caller W. -/
lemma exists_raising_multiplier_graph_room (hreg : FixedDirichletRegularity)
    (hKernel : UnitBallValueTraceKernel τ0) (δ0 : ℝ) (hδ0 : 0 < δ0) (W : CoeffRoom δ0) :
    ∃ dU : ℝ, 0 < dU ∧ ∀ V : Generator, ∀ c : RetainedCoefficient, ∀ t ∈ ParamRoom dU, ∀ x : Hi,
      IH (GH δ0 W V c t x) = generatorHigh V (NH (QW δ0 W c t) x) -
        NL (smoothMultiplierLowerJets (QW δ0 W c t)) (generatorHigh V x) := by
  obtain ⟨dU,hdU,_hdU0,_hdUρ,_hUS,hUG,_hUC⟩ :=
    exists_commonRoom_retained_generator_multiplier_gains g L y0 Φ B ε C ρ H a w hData hg hcalc
      hF hO hD τ0 hreg hKernel δ0 hδ0 W
  refine ⟨dU,hdU,?_⟩
  intro V c t ht x
  exact (hUG V c t ht).1 x

/-- Root: combine existential graph rooms without elaborating their proposition payloads. -/
private lemma combine_graph_rooms {D U G : Type*} {A B C : D → Prop} {Q : D → G → Prop}
    {P : U → Prop} {T : U → Prop} {Result : Prop}
    (hA : ∃ d : D, A d ∧ B d ∧ C d ∧ ∃ g : G, Q d g)
    (hU : ∃ u : U, P u ∧ T u)
    (f : ∀ d u g, A d → B d → C d → Q d g → P u → T u → Result) : Result := by
  rcases hA with ⟨d,ha,hb,hc,g,hq⟩
  rcases hU with ⟨u,hp,ht⟩
  exact f d u g ha hb hc hq hp ht

theorem exists_commonRoom_actual_raisingE_high_graph
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0)
    (δ0 : ℝ) (hδ0 : 0 < δ0) (W : CoeffRoom δ0) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ0 ∧ δ ≤ ρ ∧
      ∀ i j : Fin 3, ∀ t ∈ ParamRoom δ, ∀ u : Hi,
        JL (CAE hreg δ0 W i j t u) = AL i (EH j t u) - EL j t (AH i u) := by
  have hA := exists_raising_coordinate_graph_room
    hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 hreg hKernel
  have hU := exists_raising_multiplier_graph_room
    hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 hreg hKernel δ0 hδ0 W
  exact combine_graph_rooms hA hU (fun dA dU G hdA hdAρ hRoomA hGG hdU hUG =>
    exists_raisingE_graph_on_given_rooms hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      hreg δ0 hδ0 W dA dU hdA hdAρ hdU hRoomA G hGG hUG)


end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualRaisingEHighGainedEndpoints
