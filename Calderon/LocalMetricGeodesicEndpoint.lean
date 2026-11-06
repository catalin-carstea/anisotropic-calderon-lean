import Calderon.LocalMetricOperatorExtension
import Calderon.CompactParameterGeodesicEndpointSecondJet
import Mathlib.Topology.Compactness.Compact
import Mathlib.Tactic

/-! SAME native local metric flow: actual operator germs transport the whole
connection and all endpoint jets of one genuine parameter flow. -/
set_option autoImplicit false
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.ConnectionError

theorem exists_smooth_parameter_local_metric_endpoint_secondJet
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] [CompleteSpace P]
    (M : P × R3 → R3 →L[ℝ] R3) (O : Set (P × R3))
    (hO : IsOpen O) (hM : ContDiffOn ℝ ∞ M O)
    (hSym : ∀ p ∈ O, ∀ X Y : R3, inner ℝ (M p X) Y = inner ℝ (M p Y) X)
    (hPos : ∀ p ∈ O, ∀ X : R3, X ≠ 0 → 0 < inner ℝ (M p X) X)
    (K : Set P) (hK : IsCompact K) (y0 : R3)
    (hCenters : ∀ q ∈ K, (q,y0) ∈ O) :
    ∃ (Phi : P → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)),
      IsOpen B ∧ (y0,0) ∈ B ∧
      ContDiff ℝ ∞ (fun p : (P × (R3 × R3)) × ℝ => Phi p.1.1 p.1.2 p.2) ∧
      (∀ q z, Phi q z 0 = z) ∧
      (∀ q z t u, Phi q z (t+u) = Phi q (Phi q z t) u) ∧
      (∀ q ∈ K, ∀ y, (y,0) ∈ B → ∀ t, Phi q (y,0) t = (y,0)) ∧
      (∀ q ∈ K, ∀ z ∈ B, ∀ t ∈ Icc (0 : ℝ) 1, (q,(Phi q z t).1) ∈ O) ∧
      (∀ q ∈ K, ∀ z ∈ B, ∀ t ∈ Icc (0 : ℝ) 1,
        HasDerivAt (Phi q z)
          (geodesicPhaseField (fun y => Ring.inverse (M (q,y)))
            (fun y => M (q,y)) (Phi q z t)) t) ∧
      ContDiff ℝ ∞ (fun p : P × (R3 × R3) => (Phi p.1 p.2 1).1) ∧
      (∀ q ∈ K, ∀ y, (y,0) ∈ B → (Phi q (y,0) 1).1 = y) ∧
      (∀ q ∈ K, ∀ y, (y,0) ∈ B →
        HasFDerivAt (fun z => (Phi q z 1).1)
          (ContinuousLinearMap.fst ℝ R3 R3+ContinuousLinearMap.snd ℝ R3 R3) (y,0)) ∧
      ∀ q ∈ K, ∀ y, (y,0) ∈ B → ∀ h k : R3 × R3,
        fderiv ℝ (fderiv ℝ (fun z => (Phi q z 1).1)) (y,0) k h =
          -(1/2 : ℝ) •
            (coordinateConnectionField (fun z => Ring.inverse (M (q,z)))
              (fun z => M (q,z)) y h.2 k.2+
             coordinateConnectionField (fun z => Ring.inverse (M (q,z)))
              (fun z => M (q,z)) y k.2 h.2) := by
  classical
  let C : Set (P × R3) := K ×ˢ {y0}
  have hC : IsCompact C := hK.prod isCompact_singleton
  have hCO : C ⊆ O := by
    rintro ⟨q,y⟩ ⟨hq,hy⟩
    have hy0 : y = y0 := mem_singleton_iff.mp hy
    subst y
    exact hCenters q hq
  obtain ⟨Mext,hMext,hQext,hSymext,hPosext,hUnit,hBoth,
      U,hU,hCU,hUO,hMGerm,hQGerm⟩ :=
    exists_contDiff_positive_operator_extension M O C hO hC hCO hM hSym hPos
  let Qext : P × R3 → R3 →L[ℝ] R3 := fun p => Ring.inverse (Mext p)
  have hQextSmooth : ContDiff ℝ ∞ Qext := hQext
  obtain ⟨Phi,B0,hB0,hb0,hPhi,hInitial,hAdd,hStationary,hODE,
      hEndpoint,hEndpointZero,hEndpointFirst,hEndpointSecond⟩ :=
    exists_smooth_parameter_geodesic_endpoint_secondJet
      Qext Mext hQextSmooth hMext K hK y0
  let Cphase : Set (P × (R3 × R3)) := K ×ˢ {(y0,0)}
  have hCphase : IsCompact Cphase := hK.prod isCompact_singleton
  have hParam : Continuous
      (fun p : (P × (R3 × R3)) × ℝ => p.1.1) := continuous_fst.fst
  have hTrace : Continuous
      (fun p : (P × (R3 × R3)) × ℝ => (p.1.1,(Phi p.1.1 p.1.2 p.2).1)) :=
    hParam.prodMk hPhi.continuous.fst
  have hTraceOpen : IsOpen
      ((fun p : (P × (R3 × R3)) × ℝ => (p.1.1,(Phi p.1.1 p.1.2 p.2).1)) ⁻¹' U) :=
    hU.preimage hTrace
  have hTraceSubset : Cphase ×ˢ Icc (0 : ℝ) 1 ⊆
      (fun p : (P × (R3 × R3)) × ℝ => (p.1.1,(Phi p.1.1 p.1.2 p.2).1)) ⁻¹' U := by
    rintro ⟨⟨q,z⟩,t⟩ ⟨⟨hq,hz⟩,ht⟩
    have hz0 : z = (y0,0) := mem_singleton_iff.mp hz
    subst z
    change (q,(Phi q (y0,0) t).1) ∈ U
    rw [hStationary q hq y0 hb0 t]
    exact hCU ⟨hq,mem_singleton y0⟩
  obtain ⟨A,J,hA,hJ,hCA,hIJ,hAJ⟩ :=
    generalized_tube_lemma hCphase isCompact_Icc hTraceOpen hTraceSubset
  obtain ⟨V,B1,hV,hB1,hKV,hB10,hVB⟩ :=
    generalized_tube_lemma hK isCompact_singleton hA hCA
  let B : Set (R3 × R3) := B0 ∩ B1
  have hB : IsOpen B := hB0.inter hB1
  have hb : (y0,0) ∈ B := ⟨hb0,hB10 (mem_singleton (y0,0))⟩
  have hRoomU (q : P) (hq : q ∈ K) (z : R3 × R3) (hz : z ∈ B)
      (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : (q,(Phi q z t).1) ∈ U :=
    hAJ (a := ((q,z),t)) ⟨hVB ⟨hKV hq,hz.2⟩,hIJ ht⟩
  have hGamma (q : P) (y : R3) (hy : (q,y) ∈ U) :
      coordinateConnectionField (fun z => Qext (q,z)) (fun z => Mext (q,z)) y =
        coordinateConnectionField (fun z => Ring.inverse (M (q,z)))
          (fun z => M (q,z)) y := by
    have hInsert : Tendsto (fun z : R3 => (q,z)) (𝓝 y) (𝓝 (q,y)) :=
      (continuous_const.prodMk continuous_id).continuousAt
    have hSpatial : (fun z => Mext (q,z)) =ᶠ[𝓝 y] (fun z => M (q,z)) :=
      (hMGerm (q,y) hy).comp_tendsto hInsert
    have hQvalue : Qext (q,y) = Ring.inverse (M (q,y)) :=
      (hQGerm (q,y) hy).self_of_nhds
    change coordinateConnectionLinearMap (Qext (q,y))
        (fderiv ℝ (fun z => Mext (q,z)) y) =
      coordinateConnectionLinearMap (Ring.inverse (M (q,y)))
        (fderiv ℝ (fun z => M (q,z)) y)
    rw [hQvalue,hSpatial.fderiv_eq]
  refine ⟨Phi,B,hB,hb,hPhi,hInitial,hAdd,?_,?_,?_,hEndpoint,?_,?_,?_⟩
  · intro q hq y hy t
    exact hStationary q hq y hy.1 t
  · intro q hq z hz t ht
    exact hUO (hRoomU q hq z hz t ht)
  · intro q hq z hz t ht
    have hd := hODE q hq z hz.1 t ht
    have hField :
        geodesicPhaseField (fun y => Qext (q,y)) (fun y => Mext (q,y)) (Phi q z t) =
          geodesicPhaseField (fun y => Ring.inverse (M (q,y)))
            (fun y => M (q,y)) (Phi q z t) := by
      change ((Phi q z t).2,
          -coordinateConnectionField (fun y => Qext (q,y))
            (fun y => Mext (q,y)) (Phi q z t).1 (Phi q z t).2 (Phi q z t).2) = _
      rw [hGamma q (Phi q z t).1 (hRoomU q hq z hz t ht)] <;> rfl
    rw [hField] at hd
    exact hd
  · intro q hq y hy
    exact hEndpointZero q hq y hy.1
  · intro q hq y hy
    exact hEndpointFirst q hq y hy.1
  · intro q hq y hy h k
    have hyU : (q,y) ∈ U := by
      have ht := hRoomU q hq (y,0) hy 0 (by simp)
      simpa only [hInitial] using ht
    have hh := hEndpointSecond q hq y hy.1 h k
    change fderiv ℝ (fderiv ℝ (fun z => (Phi q z 1).1)) (y,0) k h =
      -(1/2 : ℝ) •
        (coordinateConnectionField (fun z => Qext (q,z)) (fun z => Mext (q,z)) y h.2 k.2 +
         coordinateConnectionField (fun z => Qext (q,z)) (fun z => Mext (q,z)) y k.2 h.2) at hh
    rw [hGamma q y hyU] at hh
    exact hh

#print axioms OAI.AnisotropicCalderon.ConnectionError.exists_smooth_parameter_local_metric_endpoint_secondJet
end OAI.AnisotropicCalderon.ConnectionError
