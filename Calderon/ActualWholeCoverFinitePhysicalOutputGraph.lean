import Calderon.ActualNativeCoverFinitePhysicalGraphs
import Calderon.ActualPhysicalOperatorFiniteSum
import Calderon.ActualSupportedPacketPhysicalCoherence
import Calderon.FiniteWeightedPhysicalGraphConvergence
import Calderon.FiniteSmoothPhysicalSourceDecomposition
import Calderon.FiniteFiveHalfSourceDecomposition
import Calderon.ActualWholeCoverPhysicalGraphSum
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
  ConformalDepth ActualScalarPrincipalAdjoint ActualFiniteHarmonicCore ReferenceDensityBounds WeightedBaseSpectral
attribute [local irreducible] sphereSobolevInclusionL referencePhysicalDensityOperator harmonicSphereSubspace
  nativePacketPhysicalDensityOperator sphereSobolevPartialSumL

private lemma tsupport_finite_physical_sum_subset
    (n:ℕ) (A:Fin n→R3→SphereL2) (K:Set R3) (hK:IsClosed K) (hSupp:∀ i,tsupport (A i)⊆K):
    tsupport (fun y => ∑ i,A i y)⊆K := by
  apply closure_minimal ?_ hK
  intro y hy
  by_contra hk
  apply hy
  exact Finset.sum_eq_zero (fun i _ => image_eq_zero_of_notMem_tsupport (fun hm => hk (hSupp i hm)))

theorem exists_actual_whole_finite_physical_graph_of_local_graphs
    (hcalc:FixedSobolevCalculus) (hreg:FixedDirichletRegularity)
    (hF:SphereFischerInner) (hO:OrthogonalSphereHarmonics) (hD:DenseSphereHarmonics)
    (tau0:UnitBallValueTrace) (hKernel:UnitBallValueTraceKernel tau0)
    (S:KnownSideSourceData) (L q delta Rstar:ℝ) (p:ℕ) (cover:NativeNormalCover S L)
    (hd:0 < delta) (hRs:0 < Rstar) (hq:q∈Icc (0:ℝ) cover.dilationCeiling)
    (hRadius:∀ y∈cylinder,referenceRadius delta Rstar p L y < cover.radiusCeiling)
    (HGraph:∀ i:Fin cover.count,∀ (u:R3→SphereSobolev (5/2:ℝ)),ContDiff ℝ ∞ u → HasCompactSupport u →
      tsupport u⊆cylinder∩(cover.packet i).centers →
      let v:R3→SphereSobolev (3/2:ℝ) := fun y => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (u y)
      ∃ (F:ℕ→R3→SphereL2) (f:R3→SphereL2),
      (∀ n:ℕ,ContDiff ℝ ∞ (F n) ∧ HasCompactSupport (F n) ∧ tsupport (F n)⊆tsupport u ∧
        ∀ y:R3,sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (sphereSobolevZeroEquiv hO hD (F n y))=
          nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover q delta Rstar p
            (fun z => sphereSobolevPartialSumL (3/2:ℝ) n (v z)) i y) ∧
      ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ tsupport f⊆tsupport u ∧
      (∀ y:R3,sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (sphereSobolevZeroEquiv hO hD (f y))=
        nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover q delta Rstar p v i y) ∧
      Tendsto (fun n:ℕ => ∫ y,referenceDensityFamily S.g1 L (q,y)*‖F n y-f y‖^2) atTop (𝓝 0))
    (u:R3→SphereSobolev (5/2:ℝ)) (hu:ContDiff ℝ ∞ u) (hc:HasCompactSupport u)
    (hSupp:tsupport u⊆interior cylinder):
    let v:R3→SphereSobolev (3/2:ℝ) := fun y => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (u y)
      ∃ (F:ℕ→R3→SphereL2) (f:R3→SphereL2),
      (∀ n:ℕ,ContDiff ℝ ∞ (F n) ∧ HasCompactSupport (F n) ∧ tsupport (F n)⊆tsupport u ∧
        ∀ i:Fin cover.count,∀ y∈interior cylinder∩(cover.packet i).centers,
          sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (sphereSobolevZeroEquiv hO hD (F n y))=
          nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover q delta Rstar p
            (fun z => sphereSobolevPartialSumL (3/2:ℝ) n (v z)) i y) ∧
      ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ tsupport f⊆tsupport u ∧
      (∀ i:Fin cover.count,∀ y∈interior cylinder∩(cover.packet i).centers,
        sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (sphereSobolevZeroEquiv hO hD (f y))=
          nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover q delta Rstar p v i y) ∧
      Tendsto (fun n:ℕ => ∫ y,referenceDensityFamily S.g1 L (q,y)*‖F n y-f y‖^2) atTop (𝓝 0) := by
  classical
  dsimp only
  let U:Fin cover.count→Set R3 := fun i => interior cylinder∩(cover.packet i).centers
  have hU:∀ i,IsOpen (U i) := fun i => isOpen_interior.inter (cover.packet i).centers_open
  have hCover:∀ y∈tsupport u,∃ i,y∈U i := by
    intro y hy
    obtain ⟨i,hi⟩ := cover.covers_cylinder y (interior_subset (hSupp hy))
    exact ⟨i,hSupp hy,hi⟩
  have hSplit:=exists_exact_smooth_finite_fiveHalf_source_decomposition cover.count u hu hc U hU hCover
  let w:Fin cover.count→R3→SphereSobolev (5/2:ℝ) := Classical.choose hSplit
  have hSplitData:=Classical.choose_spec hSplit
  have hw:∀ i,ContDiff ℝ ∞ (w i) ∧ HasCompactSupport (w i) ∧ tsupport (w i)⊆tsupport u∩U i := hSplitData.1
  have hSum:=hSplitData.2
  have hRoom (i:Fin cover.count):tsupport (w i)⊆cylinder∩(cover.packet i).centers := by
    intro y hy
    exact ⟨interior_subset ((hw i).2.2 hy).2.1,((hw i).2.2 hy).2.2⟩
  have hEach (i:Fin cover.count):=HGraph i (w i) (hw i).1 (hw i).2.1 (hRoom i)
  dsimp only at hEach
  choose A a hOutputData using hEach
  have hA (i:Fin cover.count):= (hOutputData i).1
  have ha (i:Fin cover.count):= (hOutputData i).2.1
  have hac (i:Fin cover.count):= (hOutputData i).2.2.1
  have has (i:Fin cover.count):= (hOutputData i).2.2.2.1
  have hag (i:Fin cover.count):= (hOutputData i).2.2.2.2.1
  have hlim (i:Fin cover.count):= (hOutputData i).2.2.2.2.2
  let I:=sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)
  let v:Fin cover.count→R3→SphereSobolev (3/2:ℝ) := fun i y => I (w i y)
  have hv (i:Fin cover.count):ContDiff ℝ ∞ (v i) := I.contDiff.comp (hw i).1
  have hvSupp (i:Fin cover.count):tsupport (v i)⊆tsupport (w i) := tsupport_comp_subset (map_zero I) (w i)
  have hSumLow: (fun y => ∑ i,v i y)=(fun y => I (u y)) := by
    funext y
    dsimp only [v]
    rw [←map_sum,hSum y]
  have hGraphSum
      (b:Fin cover.count→R3→SphereSobolev (3/2:ℝ)) (hb:∀ i,ContDiff ℝ ∞ (b i))
      (hbs:∀ i,tsupport (b i)⊆tsupport (w i)) (B:Fin cover.count→R3→SphereL2)
      (hB:∀ i y,sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (sphereSobolevZeroEquiv hO hD (B i y))=
        nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover q delta Rstar p (b i) i y):
      ∀ j:Fin cover.count,∀ y∈interior cylinder∩(cover.packet j).centers,
        sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (sphereSobolevZeroEquiv hO hD (∑ i,B i y))=
          nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover q delta Rstar p
            (fun z => ∑ i,b i z) j y := by
    intro j y hy
    exact nativePacketPhysicalDensityOperator_sum_of_supported_graphs hcalc hreg hF hO hD tau0 hKernel S L q delta Rstar p
      cover hd hRs hq (fun i => tsupport (w i)) (fun i t ht => ((hw i).2.2 ht).2.2)
      b hb hbs B hB j y hy.2 (hRadius y (interior_subset hy.1))
  let F:ℕ→R3→SphereL2 := fun n y => ∑ i,A i n y
  let f:R3→SphereL2 := fun y => ∑ i,a i y
  have hFSmooth (n:ℕ):ContDiff ℝ ∞ (F n) := ContDiff.sum (fun i _ => (hA i n).1)
  have hfSmooth:ContDiff ℝ ∞ f := ContDiff.sum (fun i _ => ha i)
  have hFSupp (n:ℕ):tsupport (F n)⊆tsupport u := tsupport_finite_physical_sum_subset cover.count (fun i => A i n)
    (tsupport u) (isClosed_tsupport u) (fun i => (hA i n).2.2.1.trans (fun t ht => ((hw i).2.2 ht).1))
  have hfSupp:tsupport f⊆tsupport u := tsupport_finite_physical_sum_subset cover.count a (tsupport u) (isClosed_tsupport u)
    (fun i => (has i).trans (fun t ht => ((hw i).2.2 ht).1))
  have hFCompact (n:ℕ):HasCompactSupport (F n) := hc.of_isClosed_subset (isClosed_tsupport _) (hFSupp n)
  have hfCompact:HasCompactSupport f := hc.of_isClosed_subset (isClosed_tsupport _) hfSupp
  refine ⟨F,f,?_,hfSmooth,hfCompact,hfSupp,?_,?_⟩
  · intro n
    refine ⟨hFSmooth n,hFCompact n,hFSupp n,?_⟩
    have h:=hGraphSum (fun i z => sphereSobolevPartialSumL (3/2:ℝ) n (v i z))
      (fun i => (sphereSobolevPartialSumL (3/2:ℝ) n).contDiff.comp (hv i))
      (fun i => (tsupport_comp_subset (map_zero (sphereSobolevPartialSumL (3/2:ℝ) n)) (v i)).trans (hvSupp i))
      (fun i => A i n) (fun i y => (hA i n).2.2.2 y)
    have hPartial:(fun z => ∑ i,sphereSobolevPartialSumL (3/2:ℝ) n (v i z))=
        (fun z => sphereSobolevPartialSumL (3/2:ℝ) n (I (u z))) := by
      funext z
      exact (map_sum (sphereSobolevPartialSumL (3/2:ℝ) n) (fun i => v i z) Finset.univ).symm.trans
        (congrArg (sphereSobolevPartialSumL (3/2:ℝ) n) (congrFun hSumLow z))
    intro j y hy
    exact (h j y hy).trans (congrArg (fun b:R3→SphereSobolev (3/2:ℝ) =>
      nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover q delta Rstar p b j y) hPartial)
  · have h:=hGraphSum v hv hvSupp a hag
    intro j y hy
    exact (h j y hy).trans (congrArg (fun b:R3→SphereSobolev (3/2:ℝ) =>
      nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover q delta Rstar p b j y) hSumLow)
  · exact tendsto_weighted_square_error_finite_sum S.g1 S.g1_admissible L q Finset.univ A a
      (fun i n => (hA i n).1.continuous) (fun i => (ha i).continuous)
      (fun i n => (hA i n).2.1) hac hlim

theorem exists_native_cover_uniform_actual_whole_finite_physical_graph
    (hcalc:FixedSobolevCalculus) (hreg:FixedDirichletRegularity)
    (hF:SphereFischerInner) (hO:OrthogonalSphereHarmonics) (hD:DenseSphereHarmonics)
    (tau0:UnitBallValueTrace) (hKernel:UnitBallValueTraceKernel tau0)
    (S:KnownSideSourceData) (L:ℝ) (hL:0 < L) (cover:NativeNormalCover S L)
    (hCenter:∀ i:Fin cover.count,∀ y∈(cover.packet i).centers,‖y-(cover.packet i).y0‖ < (cover.packet i).rho):
    ∃ p0:ℕ,2 ≤ p0 ∧ ∃ eps0:ℝ,0 < eps0 ∧ eps0 ≤ 1 ∧
      ∀ p:ℕ,p0 ≤ p → ∀ q∈Icc (0:ℝ) cover.dilationCeiling,
      ∀ delta:ℝ,0 < delta → delta ≤ 1 → ∀ Rstar:ℝ,0 < Rstar →
      ∀ eps:ℝ,0 ≤ eps → eps ≤ eps0 → CurrentRadiusBootstrap S L q delta Rstar eps p →
      (∀ y∈cylinder,referenceRadius delta Rstar p L y < cover.radiusCeiling) ∧
      ∀ (u:R3→SphereSobolev (5/2:ℝ)),ContDiff ℝ ∞ u → HasCompactSupport u → tsupport u⊆interior cylinder →
      let v:R3→SphereSobolev (3/2:ℝ) := fun y => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (u y)
      ∃ (F:ℕ→R3→SphereL2) (f:R3→SphereL2),
      (∀ n:ℕ,ContDiff ℝ ∞ (F n) ∧ HasCompactSupport (F n) ∧ tsupport (F n)⊆tsupport u ∧
        ∀ i:Fin cover.count,∀ y∈interior cylinder∩(cover.packet i).centers,
          sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (sphereSobolevZeroEquiv hO hD (F n y))=
          nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover q delta Rstar p
            (fun z => sphereSobolevPartialSumL (3/2:ℝ) n (v z)) i y) ∧
      ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ tsupport f⊆tsupport u ∧
      (∀ i:Fin cover.count,∀ y∈interior cylinder∩(cover.packet i).centers,
        sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (sphereSobolevZeroEquiv hO hD (f y))=
          nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover q delta Rstar p v i y) ∧
      Tendsto (fun n:ℕ => ∫ y,referenceDensityFamily S.g1 L (q,y)*‖F n y-f y‖^2) atTop (𝓝 0) := by
  classical
  obtain ⟨p0,hp0,eps0,heps0,heps01,HLocal⟩ := exists_native_cover_uniform_actual_local_finite_physical_graphs
    hcalc hreg hF hO hD tau0 hKernel S L hL cover hCenter
  refine Exists.intro p0 ?_
  refine And.intro hp0 ?_
  refine Exists.intro eps0 ?_
  refine And.intro heps0 ?_
  refine And.intro heps01 ?_
  intro p hp q hq delta hd hd1 Rstar hRs eps heps heps0' hBoot
  obtain ⟨hRadius,HGraph⟩ := HLocal p hp q hq delta hd hd1 Rstar hRs eps heps heps0' hBoot
  refine ⟨hRadius,?_⟩
  intro u hu hc hSupp
  exact exists_actual_whole_finite_physical_graph_of_local_graphs hcalc hreg hF hO hD tau0 hKernel
    S L q delta Rstar p cover hd hRs hq hRadius HGraph u hu hc hSupp

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
