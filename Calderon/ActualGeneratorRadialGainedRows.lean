import Calderon.ActualRetainedGeneratorMultiplierGains

/-! Source-only Sol author prerequisite for W/E. Upfront:
generator-radial-before-v001. Actual Th/Tl/Sh/Sl and physical degree k. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualGeneratorRadialGainedRows
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualRetainedGeneratorMultiplierGains
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "Pphys" => ℝ × (R3 × ℝ)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
  (hreg : FixedDirichletRegularity)
local notation "Th" => adjointHighRemainder hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "Tl" => adjointHalfRemainder hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "Sh" => sharpRemainder hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "Sl" => lowerSharpRemainder hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "Ω" => referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0

def generatorAdjointRadialHigh (V : Generator) (p : Pphys) : Hi →L[ℝ] Half :=
  match V with
  | Sum.inl ij => adjointRotationGain hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData ij.1 ij.2 p
  | Sum.inr _ => adjointDegreeGain hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg p

def generatorSharpRadialHigh (V : Generator) (p : Pphys) : Hi →L[ℝ] Half :=
  match V with
  | Sum.inl ij => referenceSharpRadialRotationSecondRemainder
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 ij.1 ij.2 p.1 p.2.1 p.2.2
  | Sum.inr _ => referenceRadialDegreeCommutatorGainedHighSecondRemainder
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 p.1 p.2.1 p.2.2
local notation "CT" => generatorAdjointRadialHigh g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg
local notation "CS" => generatorSharpRadialHigh g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg

/-- Both literal actual radial high gained graphs for every constant generator. -/
theorem generatorRadialHigh_graphs (V : Generator) (p : Pphys)
    (hSeg : ∀ θ ∈ Icc (0 : ℝ) 1, (p.1,(p.2.1,θ*p.2.2)) ∈ Ω) (u : Hi) :
    JL (CT V p u)=generatorLow V (Th p u)-Tl p (generatorHigh V u) ∧
    JL (CS V p u)=generatorLow V (Sh p u)-Sl p (generatorHigh V u) := by
  cases V with
  | inl ij =>
    exact ⟨(referenceAdjointHighAngleSecondRemainder_completed_rotation_graph
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg ij.1 ij.2 p.1 p.2.1 p.2.2 hSeg u).symm,
      referenceSharpRadialRotationSecondRemainder_weak_graph
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 ij.1 ij.2 p.1 p.2.1 p.2.2 hSeg u⟩
  | inr z =>
    refine ⟨RawAdjointDegreeGainDraft.gainedHighSecondRemainder_signed_adjoint_degree_graph
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 p.1 p.2.1 p.2.2 hSeg u,?_⟩
    have hc := DFunLike.congr_fun
      (referenceRadialDegreeCommutatorGainedHighSecondRemainder_lower_compatibility
        g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 p.1 p.2.1 p.2.2 hSeg) u
    rw [ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply] at hc
    exact hc.trans (referenceRadialDegreeCommutatorHalfSecondRemainder_raw_degree_graph
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 p.1 p.2.1 p.2.2 hSeg u)

/-- Actual total joint regularity, retaining original signed Taylor definitions. -/
theorem generatorRadialHigh_contDiffAt (V : Generator) (p : Pphys)
    (hSeg : ∀ θ ∈ Icc (0 : ℝ) 1, (p.1,(p.2.1,θ*p.2.2)) ∈ Ω) :
    ContDiffAt ℝ ∞ (CT V) p ∧ ContDiffAt ℝ ∞ (CS V) p := by
  cases V with
  | inl ij =>
    exact ⟨contDiffAt_adjointRotationGain hcalc hF hO hD τ0
      g L y0 Φ B ε C ρ H a w hData hreg ij.1 ij.2 p hSeg,
      contDiffAt_sharpRotationGain hcalc hF hO hD τ0
        g L y0 Φ B ε C ρ H a w hData ij.1 ij.2 p hSeg⟩
  | inr z =>
    exact ⟨RawAdjointDegreeGainDraft.contDiffAt_gainedHighSecondRemainder_of_segment
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 p.1 p.2.1 p.2.2 hSeg,
      contDiffAt_referenceRadialDegreeCommutatorGainedHighSecondRemainder_of_segment
        g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 p.1 p.2.1 p.2.2 hSeg⟩

/-- One actual common room for all rotation/physical-degree forward and sharp
radial high gains, literal graphs, joint smoothness and every finite joint cap. -/
private def actualGeneratorRadialFoldedContract : Prop :=
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ρ ∧ commonRoom y0 ρ δ ⊆ Ω ∧
      (∀ V : Generator, ContDiffOn ℝ ∞ (CT V) (commonRoom y0 ρ δ) ∧
        ContDiffOn ℝ ∞ (CS V) (commonRoom y0 ρ δ)) ∧
      (∀ V : Generator, ∀ p ∈ commonRoom y0 ρ δ, ∀ u : Hi,
        JL (CT V p u)=generatorLow V (Th p u)-Tl p (generatorHigh V u) ∧
        JL (CS V p u)=generatorLow V (Sh p u)-Sl p (generatorHigh V u)) ∧
      (∀ N : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ V : Generator, ∀ n : ℕ, n ≤ N → ∀ p ∈ commonRoom y0 ρ δ,
        ‖iteratedFDerivWithin ℝ n (CT V) (commonRoom y0 ρ δ) p‖ ≤ M ∧
        ‖iteratedFDerivWithin ℝ n (CS V) (commonRoom y0 ρ δ) p‖ ≤ M)
attribute [local irreducible] actualGeneratorRadialFoldedContract
private theorem actualGeneratorRadialFoldedContract_proof :
    actualGeneratorRadialFoldedContract g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg := by
  classical
  obtain ⟨lam,Lam,δ,_hlam,hδ,hδρ,hFin⟩ := exists_finiteRoomGuard
    hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg
  have hRoom : commonRoom y0 ρ δ ⊆ Ω := fun p hp => (hFin p hp).2.2.1
  have hSeg (p : Pphys) (hp : p ∈ commonRoom y0 ρ δ) :=
    segment_of_mem_commonRoom hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hRoom p hp
  have hSm (V : Generator) : ContDiffOn ℝ ∞ (CT V) (commonRoom y0 ρ δ) ∧
      ContDiffOn ℝ ∞ (CS V) (commonRoom y0 ρ δ) :=
    ⟨fun p hp => (generatorRadialHigh_contDiffAt g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg V p (hSeg p hp)).1.contDiffWithinAt,
     fun p hp => (generatorRadialHigh_contDiffAt g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg V p (hSeg p hp)).2.contDiffWithinAt⟩
  have hK := isCompact_commonRoom y0 ρ δ
  have hU := uniqueDiffOn_commonRoom y0 ρ hData.1.2.1 hδ
  unfold actualGeneratorRadialFoldedContract
  refine ⟨δ,hδ,hδρ,hRoom,hSm,?_,?_⟩
  · exact fun V p hp u => generatorRadialHigh_graphs g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg V p (hSeg p hp) u
  · intro N
    choose MT hMT using fun V : Generator =>
      exists_compact_iteratedFDerivWithin_bound (CT V) (commonRoom y0 ρ δ) hK hU (hSm V).1 N
    choose MS hMS using fun V : Generator =>
      exists_compact_iteratedFDerivWithin_bound (CS V) (commonRoom y0 ρ δ) hK hU (hSm V).2 N
    let M := ∑ V : Generator, (MT V+MS V)
    refine ⟨M,Finset.sum_nonneg (fun V _ => add_nonneg (hMT V).1 (hMS V).1),?_⟩
    intro V n hn p hp
    have hOne : MT V+MS V ≤ M :=
      Finset.single_le_sum (fun W _ => add_nonneg (hMT W).1 (hMS W).1) (Finset.mem_univ V)
    have hT := (hMT V).2 n hn p hp
    have hS := (hMS V).2 n hn p hp
    have hT0 := (hMT V).1
    have hS0 := (hMS V).1
    exact ⟨hT.trans (by linarith),hS.trans (by linarith)⟩


theorem exists_commonRoom_actual_generator_radial_high_gains :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ρ ∧ commonRoom y0 ρ δ ⊆ Ω ∧
      (∀ V : Generator, ContDiffOn ℝ ∞ (CT V) (commonRoom y0 ρ δ) ∧
        ContDiffOn ℝ ∞ (CS V) (commonRoom y0 ρ δ)) ∧
      (∀ V : Generator, ∀ p ∈ commonRoom y0 ρ δ, ∀ u : Hi,
        JL (CT V p u)=generatorLow V (Th p u)-Tl p (generatorHigh V u) ∧
        JL (CS V p u)=generatorLow V (Sh p u)-Sl p (generatorHigh V u)) ∧
      (∀ N : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ V : Generator, ∀ n : ℕ, n ≤ N → ∀ p ∈ commonRoom y0 ρ δ,
        ‖iteratedFDerivWithin ℝ n (CT V) (commonRoom y0 ρ δ) p‖ ≤ M ∧
        ‖iteratedFDerivWithin ℝ n (CS V) (commonRoom y0 ρ δ) p‖ ≤ M) := by
  simpa only [actualGeneratorRadialFoldedContract] using (actualGeneratorRadialFoldedContract_proof g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualGeneratorRadialGainedRows
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualGeneratorRadialGainedRows.exists_commonRoom_actual_generator_radial_high_gains
