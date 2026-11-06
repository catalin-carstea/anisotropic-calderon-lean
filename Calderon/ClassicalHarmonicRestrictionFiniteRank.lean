import Calderon.ClassicalHarmonicL2Space
import Calderon.ClassicalDilatedMetricHarmonicL2Closure
import Calderon.ClassicalDilatedMetricHarmonicL2Jets
import Calderon.UniformBufferedHarmonicJetBounds
import Calderon.UniformBufferedHarmonicTaylorBounds
import Calderon.MetricSmooth
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Calderon.FiniteHalfOpenCubePartition
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.DenseEmbedding

noncomputable section
set_option autoImplicit false
open Set Metric MeasureTheory Filter
open scoped ContDiff Topology ENNReal BigOperators Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.Regularity
open EnergyBridge
open TopologicalSpace (Compacts)

private theorem classical_dilated_metric_harmonic_L2_representative
    (a : MatrixField) (ha : IsAdmissibleMetric a) (lambda : ℝ)
    (D : Set R3) (hD : IsOpen D) :
    let A : MatrixField := principalCoefficient (fun y : R3 => a (lambda • y))
    let hA : ContDiffOn ℝ ∞ A D :=
      ((contDiff_principalCoefficient a ha).comp (contDiff_const_smul lambda)).contDiffOn
    let H := classicalHarmonicL2Space D hD A hA
    ∀ w : H, ∃ f : R3 → ℝ, ContDiffOn ℝ ∞ f D ∧
      (∀ x ∈ D, divCoeffGrad A f x = 0) ∧
      ∃ hf : MemLp f 2 ((volume : Measure R3).restrict D),
        hf.toLp f = (w : Lp ℝ 2 ((volume : Measure R3).restrict D)) := by
  exact (classicalDilatedMetricHarmonicL2Submodule_closure_and_representatives a ha lambda D hD).2.2.2.1

private theorem exists_compact_jet_map_of_representatives
    (D : Set R3) (hD : IsOpen D) (A : MatrixField)
    (H : ClosedSubmodule ℝ (Lp ℝ 2 ((volume : Measure R3).restrict D)))
    (m : ℕ) (K : Compacts R3) (hKD : ∀ x : K, (x : R3) ∈ D)
    (J : ℝ) (hJ : 0 < J) (rep : H → R3 → ℝ)
    (hSmooth : ∀ w : H, ContDiffOn ℝ ∞ (rep w) D)
    (hMem : ∀ w : H, MemLp (rep w) 2 ((volume : Measure R3).restrict D))
    (hClass : ∀ w : H, (hMem w).toLp (rep w) = (w : Lp ℝ 2 ((volume : Measure R3).restrict D)))
    (hBound : ∀ (w : H) (x : K), ‖iteratedFDeriv ℝ m (rep w) (x : R3)‖ ≤ J * ‖w‖) :
        letI : CompactSpace K := TopologicalSpace.Compacts.instCompactSpaceSubtypeMem K
        letI : SeminormedAddCommGroup (ContinuousMultilinearMap ℝ (fun _ : Fin m => R3) ℝ) :=
          ContinuousMultilinearMap.seminormedAddCommGroup (𝕜 := ℝ)
            (E := fun _ : Fin m => R3) (G := ℝ)
        letI : NormedSpace ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin m => R3) ℝ) :=
          ContinuousMultilinearMap.normedSpace (𝕜 := ℝ) (𝕜' := ℝ)
            (E := fun _ : Fin m => R3) (G := ℝ)
        letI : SeminormedAddCommGroup C(K, ContinuousMultilinearMap ℝ (fun _ : Fin m => R3) ℝ) :=
          ContinuousMap.instSeminormedAddCommGroup
        letI : NormedSpace ℝ C(K, ContinuousMultilinearMap ℝ (fun _ : Fin m => R3) ℝ) := ContinuousMap.normedSpace
        letI : NormedSpace ℝ H := ClosedSubmodule.normedSpace H
        ∃ E : H →L[ℝ] C(K, ContinuousMultilinearMap ℝ (fun _ : Fin m => R3) ℝ),
          ‖E‖ ≤ J ∧
          ∀ (w : H) (f : R3 → ℝ), ContDiffOn ℝ ∞ f D →
            (∀ x ∈ D, divCoeffGrad A f x = 0) →
            ∀ hf : MemLp f 2 ((volume : Measure R3).restrict D),
              hf.toLp f = (w : Lp ℝ 2 ((volume : Measure R3).restrict D)) →
              ∀ x : K, E w x = iteratedFDeriv ℝ m f (x : R3) := by
  classical
  letI : CompactSpace K := TopologicalSpace.Compacts.instCompactSpaceSubtypeMem K
  letI : SeminormedAddCommGroup (ContinuousMultilinearMap ℝ (fun _ : Fin m => R3) ℝ) :=
    ContinuousMultilinearMap.seminormedAddCommGroup (𝕜 := ℝ)
      (E := fun _ : Fin m => R3) (G := ℝ)
  letI : NormedSpace ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin m => R3) ℝ) :=
    ContinuousMultilinearMap.normedSpace (𝕜 := ℝ) (𝕜' := ℝ)
      (E := fun _ : Fin m => R3) (G := ℝ)
  letI : SeminormedAddCommGroup C(K, ContinuousMultilinearMap ℝ (fun _ : Fin m => R3) ℝ) :=
    ContinuousMap.instSeminormedAddCommGroup
  letI : NormedSpace ℝ C(K, ContinuousMultilinearMap ℝ (fun _ : Fin m => R3) ℝ) := ContinuousMap.normedSpace
  letI : NormedSpace ℝ H := ClosedSubmodule.normedSpace H
  have hAE (w : H) :
      ((w : Lp ℝ 2 ((volume : Measure R3).restrict D)) : R3 → ℝ)
        =ᵐ[(volume : Measure R3).restrict D] rep w := by
    have h := (hMem w).coeFn_toLp
    rw [hClass w] at h
    exact h
  have hJetEq (f g : R3 → ℝ) (hf : ContDiffOn ℝ ∞ f D)
      (hg : ContDiffOn ℝ ∞ g D)
      (heq : f =ᵐ[(volume : Measure R3).restrict D] g) (x : K) :
      iteratedFDeriv ℝ m f (x : R3) = iteratedFDeriv ℝ m g (x : R3) := by
    have hfg : EqOn f g D :=
      Measure.eqOn_open_of_ae_eq heq hD hf.continuousOn hg.continuousOn
    have hgerm : f =ᶠ[nhds (x : R3)] g :=
      Filter.eventually_of_mem (hD.mem_nhds (hKD x)) (fun _ hx => hfg hx)
    exact (hgerm.iteratedFDeriv ℝ m).eq_of_nhds
  let value : H → C(K, ContinuousMultilinearMap ℝ (fun _ : Fin m => R3) ℝ) :=
    fun w => ⟨fun x => iteratedFDeriv ℝ m (rep w) (x : R3), by
      have hc : ContinuousOn (iteratedFDeriv ℝ m (rep w)) D :=
        ContinuousOn.continuousOn_iteratedFDeriv (hSmooth w) hD (by simp)
      exact hc.comp_continuous continuous_subtype_val hKD⟩
  let F : H →ₗ[ℝ] C(K, ContinuousMultilinearMap ℝ (fun _ : Fin m => R3) ℝ) :=
    { toFun := value
      map_add' := by
        intro u v
        have hSum : rep (u + v) =ᵐ[(volume : Measure R3).restrict D] rep u + rep v := by
          filter_upwards [hAE (u + v), hAE u, hAE v,
            Lp.coeFn_add (u : Lp ℝ 2 ((volume : Measure R3).restrict D))
              (v : Lp ℝ 2 ((volume : Measure R3).restrict D))] with x huv hu hv hadd
          change ((u : Lp ℝ 2 ((volume : Measure R3).restrict D)) +
            (v : Lp ℝ 2 ((volume : Measure R3).restrict D))) x = rep (u + v) x at huv
          exact huv.symm.trans (hadd.trans (congrArg₂ (fun r s : ℝ => r + s) hu hv))
        apply ContinuousMap.ext
        intro x
        change iteratedFDeriv ℝ m (rep (u + v)) (x : R3) =
          iteratedFDeriv ℝ m (rep u) (x : R3) + iteratedFDeriv ℝ m (rep v) (x : R3)
        exact (hJetEq _ _ (hSmooth (u + v)) ((hSmooth u).add (hSmooth v)) hSum x).trans
          (iteratedFDeriv_add_apply
            ((hSmooth u).contDiffAt (hD.mem_nhds (hKD x)) |>.of_le (by simp))
            ((hSmooth v).contDiffAt (hD.mem_nhds (hKD x)) |>.of_le (by simp)))
      map_smul' := by
        intro r u
        have hSmul : rep (r • u) =ᵐ[(volume : Measure R3).restrict D] r • rep u := by
          filter_upwards [hAE (r • u), hAE u,
            Lp.coeFn_smul r (u : Lp ℝ 2 ((volume : Measure R3).restrict D))] with x hru hu hsmul
          change (r • (u : Lp ℝ 2 ((volume : Measure R3).restrict D))) x = rep (r • u) x at hru
          exact hru.symm.trans (hsmul.trans (congrArg (fun s : ℝ => r * s) hu))
        apply ContinuousMap.ext
        intro x
        change iteratedFDeriv ℝ m (rep (r • u)) (x : R3) =
          r • iteratedFDeriv ℝ m (rep u) (x : R3)
        exact (hJetEq _ _ (hSmooth (r • u)) ((hSmooth u).const_smul r) hSmul x).trans
          (iteratedFDeriv_const_smul_apply' (𝕜 := ℝ) (i := m) (a := r)
            (f := rep u) (x := (x : R3))
            ((hSmooth u).contDiffAt (hD.mem_nhds (hKD x)) |>.of_le (by simp))) }
  have hFPointwise (w : H) (x : K) : ‖(F w) x‖ ≤ J * ‖w‖ := hBound w x
  have hFNormCriterion (w : H) :
      (‖F w‖ ≤ J * ‖w‖) ↔ (∀ x : K, ‖(F w) x‖ ≤ J * ‖w‖) :=
    ContinuousMap.norm_le (F w) (mul_nonneg hJ.le (norm_nonneg w))
  have hFBound (w : H) : ‖F w‖ ≤ J * ‖w‖ :=
    (hFNormCriterion w).mpr (hFPointwise w)
  let E : H →L[ℝ] C(K, ContinuousMultilinearMap ℝ (fun _ : Fin m => R3) ℝ) :=
    LinearMap.mkContinuous (𝕜 := ℝ) (𝕜₂ := ℝ) (E := H)
      (F := C(K, ContinuousMultilinearMap ℝ (fun _ : Fin m => R3) ℝ)) (σ := RingHom.id ℝ)
      F J (fun w : H => hFBound w)
  have hENorm : ‖E‖ ≤ J :=
    LinearMap.mkContinuous_norm_le (E := H)
      (F := C(K, ContinuousMultilinearMap ℝ (fun _ : Fin m => R3) ℝ)) F hJ.le (fun w : H => hFBound w)
  refine ⟨E, hENorm, ?_⟩
  intro w f hf hPf hfMem hfClass x
  have hAF : ((w : Lp ℝ 2 ((volume : Measure R3).restrict D)) : R3 → ℝ)
      =ᵐ[(volume : Measure R3).restrict D] f := by
    have h := hfMem.coeFn_toLp
    rw [hfClass] at h
    exact h
  change iteratedFDeriv ℝ m (rep w) (x : R3) = iteratedFDeriv ℝ m f (x : R3)
  exact hJetEq _ _ (hSmooth w) hf ((hAE w).symm.trans hAF) x

private theorem exists_uniform_dilated_metric_harmonic_compact_jet_maps
    (a : MatrixField) (ha : IsAdmissibleMetric a) (B : ℝ) (hB : 0 < B) :
    ∃ lambda0 : ℝ, 0 < lambda0 ∧ lambda0 ≤ 1 ∧
      ∀ (m : ℕ) (d : ℝ), 0 < d →
        ∃ J : ℝ, 0 < J ∧
        ∀ lambda : ℝ, lambda ∈ Icc (0 : ℝ) lambda0 →
        ∀ (D : Set R3) (hD : IsOpen D), D ⊆ ball (0 : R3) B →
        let A : MatrixField := principalCoefficient (fun y : R3 => a (lambda • y))
        let hA : ContDiffOn ℝ ∞ A D :=
          ((contDiff_principalCoefficient (a) (ha)).comp
            (contDiff_const_smul lambda)).contDiffOn
        let H := classicalHarmonicL2Space D hD A hA
        ∀ K : Compacts R3, (∀ x ∈ (K : Set R3), closedBall x d ⊆ D) →
        letI : CompactSpace K := TopologicalSpace.Compacts.instCompactSpaceSubtypeMem K
        letI : SeminormedAddCommGroup (ContinuousMultilinearMap ℝ (fun _ : Fin m => R3) ℝ) :=
          ContinuousMultilinearMap.seminormedAddCommGroup (𝕜 := ℝ)
            (E := fun _ : Fin m => R3) (G := ℝ)
        letI : NormedSpace ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin m => R3) ℝ) :=
          ContinuousMultilinearMap.normedSpace (𝕜 := ℝ) (𝕜' := ℝ)
            (E := fun _ : Fin m => R3) (G := ℝ)
        letI : SeminormedAddCommGroup C(K, ContinuousMultilinearMap ℝ (fun _ : Fin m => R3) ℝ) :=
          ContinuousMap.instSeminormedAddCommGroup
        letI : NormedSpace ℝ C(K, ContinuousMultilinearMap ℝ (fun _ : Fin m => R3) ℝ) := ContinuousMap.normedSpace
        letI : NormedSpace ℝ H := ClosedSubmodule.normedSpace H
        ∃ E : H →L[ℝ] C(K, ContinuousMultilinearMap ℝ (fun _ : Fin m => R3) ℝ),
          ‖E‖ ≤ J ∧
          ∀ (w : H) (f : R3 → ℝ), ContDiffOn ℝ ∞ f D →
            (∀ x ∈ D, divCoeffGrad A f x = 0) →
            ∀ hf : MemLp f 2 ((volume : Measure R3).restrict D),
              hf.toLp f = (w : Lp ℝ 2 ((volume : Measure R3).restrict D)) →
              ∀ x : K, E w x = iteratedFDeriv ℝ m f (x : R3) := by
  classical
  obtain ⟨lambda0, hLambda0, hLambda0One, hJet⟩ :=
    exists_uniform_dilated_metric_buffered_harmonic_jet_bound a ha B hB
  refine ⟨lambda0, hLambda0, hLambda0One, ?_⟩
  intro m d hd
  obtain ⟨J, hJ, hBound⟩ := hJet m d hd
  refine ⟨J, hJ, ?_⟩
  intro lambda hLambda D hD hDB A hA H K hK
  letI : CompactSpace K := TopologicalSpace.Compacts.instCompactSpaceSubtypeMem K
  letI : SeminormedAddCommGroup (ContinuousMultilinearMap ℝ (fun _ : Fin m => R3) ℝ) :=
    ContinuousMultilinearMap.seminormedAddCommGroup (𝕜 := ℝ)
      (E := fun _ : Fin m => R3) (G := ℝ)
  letI : NormedSpace ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin m => R3) ℝ) :=
    ContinuousMultilinearMap.normedSpace (𝕜 := ℝ) (𝕜' := ℝ)
      (E := fun _ : Fin m => R3) (G := ℝ)
  letI : SeminormedAddCommGroup C(K, ContinuousMultilinearMap ℝ (fun _ : Fin m => R3) ℝ) :=
    ContinuousMap.instSeminormedAddCommGroup
  letI : NormedSpace ℝ C(K, ContinuousMultilinearMap ℝ (fun _ : Fin m => R3) ℝ) := ContinuousMap.normedSpace
  letI : NormedSpace ℝ H := ClosedSubmodule.normedSpace H
  have hKD (x : K) : (x : R3) ∈ D :=
    hK x x.property (mem_closedBall_self hd.le)
  have hRep := classical_dilated_metric_harmonic_L2_representative a ha lambda D hD
  choose rep hSmooth hPDE hMem hClass using hRep
  have hRepNorm (w : H) :
      (eLpNorm (rep w) 2 ((volume : Measure R3).restrict D)).toReal = ‖w‖ := by
    calc
      _ = ‖(hMem w).toLp (rep w)‖ := (Lp.norm_toLp _ _).symm
      _ = ‖(w : Lp ℝ 2 ((volume : Measure R3).restrict D))‖ := congrArg norm (hClass w)
      _ = ‖w‖ := rfl
  have hBoundRep (w : H) (x : K) :
      ‖iteratedFDeriv ℝ m (rep w) (x : R3)‖ ≤ J * ‖w‖ := by
    have hb := hBound lambda hLambda D hD hDB (rep w)
      (hSmooth w) (hPDE w) (hMem w) (x : R3) (hK x x.property)
    exact hb.trans_eq (congrArg (fun q : ℝ => J * q) (hRepNorm w))
  exact exists_compact_jet_map_of_representatives D hD A H m K hKD J hJ rep hSmooth hMem hClass hBoundRep

private theorem exists_buffered_finite_half_open_cube_partition
    (B : ℝ) (hB : 0 < B) (n : ℕ) (hn : 1 ≤ n)
    (S : Set R3) (hS : IsOpen S) (hSB : S ⊆ ball (0 : R3) B)
    (D : Set R3) (d : ℝ) (hd : 0 < d)
    (hBuffer : ∀ x ∈ closure S, closedBall x (2 * d) ⊆ D) :
    let cell : (Fin 3 → ℤ) → Set R3 := fun nu =>
      S ∩ {x : R3 | ∀ r : Fin 3,
        (nu r : ℝ) / (n : ℝ) ≤ x r ∧ x r < ((nu r : ℝ) + 1) / (n : ℝ)}
    ∃ I : Finset (Fin 3 → ℤ),
    ∃ center : {nu : Fin 3 → ℤ // nu ∈ I} → R3,
      (∀ nu : {nu : Fin 3 → ℤ // nu ∈ I}, center nu ∈ cell nu.val) ∧
      (S = ⋃ nu ∈ (I : Set (Fin 3 → ℤ)), cell nu) ∧
      (∀ nu ∈ I, ∀ mu ∈ I, nu ≠ mu → Disjoint (cell nu) (cell mu)) ∧
      (∀ nu : Fin 3 → ℤ, MeasurableSet (cell nu)) ∧
      (∀ nu ∈ I, ∀ x ∈ cell nu, ∀ y ∈ cell nu,
        dist x y ≤ Real.sqrt 3 / (n : ℝ)) ∧
      I.card ≤ Nat.ceil ((2 * B + 4) ^ 3) * n ^ 3 ∧
      ∀ nu : {nu : Fin 3 → ℤ // nu ∈ I}, closedBall (center nu) (2 * d) ⊆ D := by
  classical
  dsimp only
  obtain ⟨I, center, _hI, hCenter, hCover, hDisjoint, hMeasurable, hDiameter, hCard, hRoom⟩ :=
    exists_finite_half_open_cube_partition B hB n hn S hSB
  exact ⟨I, center, hCenter, hCover, hDisjoint, hMeasurable hS, hDiameter, hCard,
    hRoom D d hd hBuffer⟩

private abbrev harmonicRestrictionCell (n : ℕ) (S : Set R3) (nu : Fin 3 → ℤ) : Set R3 :=
  S ∩ {x : R3 | ∀ r : Fin 3,
    (nu r : ℝ) / (n : ℝ) ≤ x r ∧ x r < ((nu r : ℝ) + 1) / (n : ℝ)}

private structure FiniteHarmonicCubePartition (B : ℝ) (n : ℕ) (S D : Set R3) (d : ℝ) where
  indices : Finset (Fin 3 → ℤ)
  center : {nu : Fin 3 → ℤ // nu ∈ indices} → R3
  center_mem : ∀ nu : {nu : Fin 3 → ℤ // nu ∈ indices},
    center nu ∈ harmonicRestrictionCell n S nu.val
  cover : S = ⋃ nu ∈ (indices : Set (Fin 3 → ℤ)), harmonicRestrictionCell n S nu
  disjoint : ∀ nu ∈ indices, ∀ mu ∈ indices, nu ≠ mu →
    Disjoint (harmonicRestrictionCell n S nu) (harmonicRestrictionCell n S mu)
  measurable : ∀ nu : Fin 3 → ℤ, MeasurableSet (harmonicRestrictionCell n S nu)
  diameter : ∀ nu ∈ indices, ∀ x ∈ harmonicRestrictionCell n S nu,
    ∀ y ∈ harmonicRestrictionCell n S nu, dist x y ≤ Real.sqrt 3 / (n : ℝ)
  card_le : indices.card ≤ Nat.ceil ((2 * B + 4) ^ 3) * n ^ 3
  room : ∀ nu : {nu : Fin 3 → ℤ // nu ∈ indices}, closedBall (center nu) (2 * d) ⊆ D

private theorem nonempty_finite_harmonic_cube_partition
    (B : ℝ) (hB : 0 < B) (n : ℕ) (hn : 1 ≤ n)
    (S : Set R3) (hS : IsOpen S) (hSB : S ⊆ ball (0 : R3) B)
    (D : Set R3) (d : ℝ) (hd : 0 < d)
    (hBuffer : ∀ x ∈ closure S, closedBall x (2 * d) ⊆ D) :
    Nonempty (FiniteHarmonicCubePartition B n S D d) := by
  classical
  obtain ⟨I, center, hCenter, hCover, hDisjoint, hMeasurable, hDiameter, hCard, hRoom⟩ :=
    exists_buffered_finite_half_open_cube_partition B hB n hn S hS hSB D d hd hBuffer
  exact ⟨⟨I, center, hCenter, hCover, hDisjoint, hMeasurable, hDiameter, hCard, hRoom⟩⟩

private theorem multilinear_diagonal_eq_sum_coordinate_words (j : ℕ)
      (M : ContinuousMultilinearMap ℝ (fun _ : Fin j => R3) ℝ) (v : R3) :
      M (fun _ : Fin j => v) =
        ∑ alpha : Fin j → Fin 3, (∏ r : Fin j, v (alpha r)) *
          M (fun r => EuclideanSpace.single (alpha r) (1 : ℝ)) := by
  classical
  have hVector (v : R3) : v = ∑ r : Fin 3, v r • EuclideanSpace.single r (1 : ℝ) := by
    apply PiLp.ext
    intro r
    have heval := map_sum (PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) r)
      (fun q : Fin 3 => v q • EuclideanSpace.single q (1 : ℝ)) Finset.univ
    change v r = (PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) r)
      (∑ q : Fin 3, v q • EuclideanSpace.single q (1 : ℝ))
    rw [heval]
    have hTerm (q : Fin 3) : (PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) r)
        (v q • EuclideanSpace.single q (1 : ℝ)) = if r = q then v q else 0 := by
      change (v q • EuclideanSpace.single q (1 : ℝ)) r = _
      simp only [PiLp.smul_apply, PiLp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    simp only [hTerm, Fintype.sum_ite_eq]
  calc
    _ = M (fun _ : Fin j => ∑ q : Fin 3, v q • EuclideanSpace.single q (1 : ℝ)) :=
      congrArg M (funext (fun _ => hVector v))
    _ = ∑ alpha : Fin j → Fin 3,
        M (fun r => v (alpha r) • EuclideanSpace.single (alpha r) (1 : ℝ)) :=
      M.toMultilinearMap.map_sum (fun _ q => v q • EuclideanSpace.single q (1 : ℝ))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro alpha _ha
      simpa only [smul_eq_mul, ContinuousMultilinearMap.coe_coe] using
        M.toMultilinearMap.map_smul_univ (fun r => v (alpha r))
          (fun r => EuclideanSpace.single (alpha r) (1 : ℝ))

private theorem finite_rank_synthesis {ι X Y : Type*} [Fintype ι]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (L : ι → X →L[ℝ] ℝ) (b : ι → Y) :
    let T : X →L[ℝ] Y := ∑ i : ι, (L i).smulRight (b i)
    FiniteDimensional ℝ (LinearMap.range T.toLinearMap) ∧
      Module.finrank ℝ (LinearMap.range T.toLinearMap) ≤ Fintype.card ι := by
  classical
  intro T
  let W : Submodule ℝ Y := Submodule.span ℝ (Set.range b)
  have hTW : LinearMap.range T.toLinearMap ≤ W := by
    rintro _ ⟨w, rfl⟩
    change T w ∈ W
    simp only [T, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply]
    exact Submodule.sum_mem W (fun i _ =>
      Submodule.smul_mem W (L i w) (Submodule.subset_span (Set.mem_range_self i)))
  letI : FiniteDimensional ℝ W := FiniteDimensional.span_of_finite ℝ (Set.finite_range b)
  refine ⟨FiniteDimensional.of_injective (Submodule.inclusion hTW)
    (Submodule.inclusion_injective hTW), ?_⟩
  exact (Submodule.finrank_mono hTW).trans (finrank_range_le_card (R := ℝ) b)

private theorem l2_norm_le_sqrt_measure_mul_of_ae_bound
    (mu : Measure R3) [IsFiniteMeasure mu] (z : Lp ℝ 2 mu)
    (C : ℝ) (hC : 0 ≤ C) (hz : ∀ᵐ x ∂mu, |z x| ≤ C) :
    ‖z‖ ≤ Real.sqrt ((mu Set.univ).toReal) * C := by
  have hzIntegral : (∫ x, (z x) ^ 2 ∂mu) = ‖z‖ ^ 2 := by
    simpa only [L2.inner_def, Real.inner_apply, ← pow_two] using (real_inner_self_eq_norm_sq z)
  have hSquare : ‖z‖ ^ 2 ≤ C ^ 2 * (mu Set.univ).toReal := by
    rw [← hzIntegral]
    calc
      _ ≤ ∫ _x : R3, C ^ 2 ∂mu :=
        integral_mono_ae (Lp.memLp z).integrable_sq (integrable_const _) (hz.mono
          (fun x hx => by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hC).mpr hx))
      _ = _ := by
        rw [integral_const]
        simp only [measureReal_def, smul_eq_mul]
        ring
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hC)).mp
  calc
    _ ≤ C ^ 2 * (mu Set.univ).toReal := hSquare
    _ = _ := by
      simp only [mul_pow, Real.sq_sqrt ENNReal.toReal_nonneg]
      ring

private theorem finite_sum_smul_toLp_ae {ι : Type*} [Fintype ι]
    (mu : Measure R3) (g : ι → R3 → ℝ) (hg : ∀ i : ι, MemLp (g i) 2 mu)
    (c : ι → ℝ) :
    ((∑ i : ι, c i • (hg i).toLp (g i) : Lp ℝ 2 mu) : R3 → ℝ) =ᵐ[mu]
      (fun x => ∑ i : ι, c i * g i x) := by
  classical
  have hBasis : ∀ᵐ x ∂mu, ∀ i : ι,
      (c i • (hg i).toLp (g i) : Lp ℝ 2 mu) x = c i * g i x := by
    apply ae_all_iff.mpr
    intro i
    filter_upwards [Lp.coeFn_smul (c i) ((hg i).toLp (g i)), (hg i).coeFn_toLp] with x hsmul hb
    calc
      _ = c i * ((hg i).toLp (g i) : R3 → ℝ) x := by
        simpa only [Pi.smul_apply, smul_eq_mul] using hsmul
      _ = c i * g i x := congrArg (fun y : ℝ => c i * y) hb
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
    (fun i : ι => c i • (hg i).toLp (g i)), hBasis] with x hsum hb
  exact hsum.trans (Finset.sum_congr rfl (fun i _ => hb i))

/- The pointwise Taylor error on the same fixed half-open grid, with all
ordered coordinate words and the original factorial normalization. -/

private theorem abs_sub_sum_indicator_taylor_le
    (B : ℝ) (n : ℕ) (_hn : 1 ≤ n) (S D : Set R3) (d : ℝ)
    (grid : FiniteHarmonicCubePartition B n S D d) (k : ℕ)
    (hMesh : Real.sqrt 3 / (n : ℝ) ≤ d / 2)
    (f : R3 → ℝ)
    (coeff : ({nu : Fin 3 → ℤ // nu ∈ grid.indices} ×
      (Σ j : Fin k, (Fin j.val → Fin 3))) → ℝ)
    (hCoeff : ∀ beta : {nu : Fin 3 → ℤ // nu ∈ grid.indices} ×
        (Σ j : Fin k, (Fin j.val → Fin 3)),
      coeff beta = iteratedFDeriv ℝ beta.2.1.val f (grid.center beta.1)
        (fun r => EuclideanSpace.single (beta.2.2 r) (1 : ℝ)))
    (CT : ℝ) (hCT : 0 ≤ CT) (N : ℝ) (hN : 0 ≤ N)
    (hTaylor :
      ∀ (nu : {nu : Fin 3 → ℤ // nu ∈ grid.indices}) (v : R3),
        ‖v‖ ≤ d / 2 →
        |f (grid.center nu + v) -
            ∑ j ∈ Finset.range k, (Nat.factorial j : ℝ)⁻¹ *
              iteratedFDeriv ℝ j f (grid.center nu) (fun _ : Fin j => v)| ≤
          CT * ‖v‖ ^ k * N) :
    ∀ (x : R3), x ∈ S →
      |f x -
          ∑ beta : {nu : Fin 3 → ℤ // nu ∈ grid.indices} ×
              (Σ j : Fin k, (Fin j.val → Fin 3)),
            coeff beta *
              ((harmonicRestrictionCell n S beta.1.val).indicator
                (fun y : R3 => (Nat.factorial beta.2.1.val : ℝ)⁻¹ *
                  ∏ r : Fin beta.2.1.val,
                    (y - grid.center beta.1) (beta.2.2 r)) x)| ≤
        CT * (Real.sqrt 3 / (n : ℝ)) ^ k * N := by
  classical
  let WordIndex := Σ j : Fin k, (Fin j.val → Fin 3)
  let Label := {nu : Fin 3 → ℤ // nu ∈ grid.indices} × WordIndex
  let p : Label → R3 → ℝ := fun beta x =>
    (Nat.factorial beta.2.1.val : ℝ)⁻¹ *
      ∏ r : Fin beta.2.1.val, (x - grid.center beta.1) (beta.2.2 r)
  let g : Label → R3 → ℝ := fun beta =>
    (harmonicRestrictionCell n S beta.1.val).indicator (p beta)
  change ∀ (x : R3), x ∈ S →
    |f x - ∑ beta : Label, coeff beta * g beta x| ≤
      CT * (Real.sqrt 3 / (n : ℝ)) ^ k * N
  intro x hx
  have hPolynomial :
      ∃ nu : {nu : Fin 3 → ℤ // nu ∈ grid.indices},
        x ∈ harmonicRestrictionCell n S nu.val ∧
          (∑ beta : Label, coeff beta * g beta x) =
            ∑ j ∈ Finset.range k, (Nat.factorial j : ℝ)⁻¹ *
              iteratedFDeriv ℝ j f (grid.center nu)
                (fun _ : Fin j => x - grid.center nu) := by
    have hxUnion : x ∈ ⋃ nu ∈ (grid.indices : Set (Fin 3 → ℤ)),
        harmonicRestrictionCell n S nu := by
      rw [← grid.cover]
      exact hx
    obtain ⟨nu, hnu⟩ := mem_iUnion.mp hxUnion
    obtain ⟨hnuI, hxnu⟩ := mem_iUnion.mp hnu
    let nu0 : {nu : Fin 3 → ℤ // nu ∈ grid.indices} := ⟨nu, hnuI⟩
    -- Give indicator rewriting the exact displayed subtype projection.
    have hxnu0 : x ∈ harmonicRestrictionCell n S nu0.val := hxnu
    refine ⟨nu0, hxnu0, ?_⟩
    change (∑ beta : {nu : Fin 3 → ℤ // nu ∈ grid.indices} × WordIndex,
      coeff beta * g beta x) = _
    rw [Fintype.sum_prod_type, Finset.sum_eq_single nu0]
    · rw [Fintype.sum_sigma, Finset.sum_range]
      apply Finset.sum_congr rfl
      intro j _hj
      calc
        (∑ alpha : Fin j.val → Fin 3,
            coeff (nu0, ⟨j, alpha⟩) * g (nu0, ⟨j, alpha⟩) x) =
            (Nat.factorial j.val : ℝ)⁻¹ *
              ∑ alpha : Fin j.val → Fin 3,
                (∏ r : Fin j.val, (x - grid.center nu0) (alpha r)) *
                  iteratedFDeriv ℝ j.val f (grid.center nu0)
                    (fun r => EuclideanSpace.single (alpha r) (1 : ℝ)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro alpha _ha
          have hIndicator :
              g (nu0, ⟨j, alpha⟩) x =
                (Nat.factorial j.val : ℝ)⁻¹ *
                  ∏ r : Fin j.val, (x - grid.center nu0) (alpha r) := by
            change (harmonicRestrictionCell n S nu0.val).indicator
              (p (nu0, ⟨j, alpha⟩)) x = _
            rw [Set.indicator_of_mem hxnu0]
          rw [hCoeff (nu0, ⟨j, alpha⟩), hIndicator]
          ring
        _ = _ :=
          congrArg (fun q : ℝ => (Nat.factorial j.val : ℝ)⁻¹ * q)
            (multilinear_diagonal_eq_sum_coordinate_words j.val
              (iteratedFDeriv ℝ j.val f (grid.center nu0))
              (x - grid.center nu0)).symm
    · intro mu _hmu hne
      apply Finset.sum_eq_zero
      intro gamma _hg
      have hval : mu.val ≠ nu0.val := fun h => hne (Subtype.ext h)
      have hxnot : x ∉ harmonicRestrictionCell n S mu.val := fun hxm =>
        Set.disjoint_left.mp
          (grid.disjoint mu.val mu.property nu0.val nu0.property hval) hxm hxnu0
      change coeff (mu, gamma) *
        (harmonicRestrictionCell n S mu.val).indicator (p (mu, gamma)) x = 0
      rw [Set.indicator_of_notMem hxnot, mul_zero]
    · simp
  obtain ⟨nu, hxnu, hpoly⟩ := hPolynomial
  have hDist : ‖x - grid.center nu‖ ≤ Real.sqrt 3 / (n : ℝ) := by
    simpa only [dist_eq_norm] using
      grid.diameter nu.val nu.property x hxnu
        (grid.center nu) (grid.center_mem nu)
  have hTaylorHere :
      |f (grid.center nu + (x - grid.center nu)) -
          ∑ j ∈ Finset.range k, (Nat.factorial j : ℝ)⁻¹ *
            iteratedFDeriv ℝ j f (grid.center nu)
              (fun _ : Fin j => x - grid.center nu)| ≤
        CT * ‖x - grid.center nu‖ ^ k * N :=
    hTaylor nu (x - grid.center nu) (hDist.trans hMesh)
  have hAdd : grid.center nu + (x - grid.center nu) = x := by abel
  rw [hAdd] at hTaylorHere
  rw [hpoly]
  calc
    _ ≤ CT * ‖x - grid.center nu‖ ^ k * N := hTaylorHere
    _ ≤ CT * (Real.sqrt 3 / (n : ℝ)) ^ k * N :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) hDist k) hCT) hN


private theorem exists_finite_rank_restriction_of_jet_taylor
    (B : ℝ) (hB : 0 < B) (k : ℕ) (hk : 1 ≤ k) (d : ℝ) (hd : 0 < d)
    (D : Set R3) (hD : IsOpen D) (hDB : D ⊆ ball (0 : R3) B) (A : MatrixField)
    (H : ClosedSubmodule ℝ (Lp ℝ 2 ((volume : Measure R3).restrict D)))
    (S0 : Submodule ℝ (Lp ℝ 2 ((volume : Measure R3).restrict D)))
    (JH : Fin (k + 1) → ℝ) (hJH : ∀ j : Fin (k + 1), 0 < JH j)
    (CT : ℝ) (hCT : 0 < CT) (e : S0 →ₗᵢ[ℝ] H) (he : DenseRange e)
    (hAmbient : ∀ u : S0,
      (e u : Lp ℝ 2 ((volume : Measure R3).restrict D)) =
        (u : Lp ℝ 2 ((volume : Measure R3).restrict D)))
    (hRaw : ∀ u : Lp ℝ 2 ((volume : Measure R3).restrict D),
      u ∈ S0 ↔ ∃ f : R3 → ℝ, ContDiffOn ℝ ∞ f D ∧
        (∀ x ∈ D, divCoeffGrad A f x = 0) ∧
        (u : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict D] f)
    (S : Set R3) (hS : IsOpen S) (hBuffer : ∀ x ∈ closure S, closedBall x (2 * d) ⊆ D)
    (hSD : S ⊆ D) (R : H →L[ℝ] Lp ℝ 2 ((volume : Measure R3).restrict S))
    (hR : ‖R‖ ≤ 1 ∧
      ∀ (w : H) (f : R3 → ℝ), ContDiffOn ℝ ∞ f D →
        (∀ x ∈ D, divCoeffGrad A f x = 0) →
        ∀ hf : MemLp f 2 ((volume : Measure R3).restrict D),
          hf.toLp f = (w : Lp ℝ 2 ((volume : Measure R3).restrict D)) →
            (R w : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict S] f)
    (hJetEval : ∀ (j : Fin (k + 1)) (c : R3), closedBall c d ⊆ D →
      ∀ alpha : Fin j.val → Fin 3, ∃ ell : S0 →L[ℝ] ℝ,
        ‖ell‖ ≤ JH j ∧
        ∀ (u : S0) (f : R3 → ℝ), ContDiffOn ℝ ∞ f D →
          (∀ x ∈ D, divCoeffGrad A f x = 0) →
          ∀ hf : MemLp f 2 ((volume : Measure R3).restrict D),
            hf.toLp f = (u : Lp ℝ 2 ((volume : Measure R3).restrict D)) →
            ell u = iteratedFDeriv ℝ j.val f c
              (fun r => EuclideanSpace.single (alpha r) (1 : ℝ)))
    (hTaylorBound : ∀ (f : R3 → ℝ), ContDiffOn ℝ ∞ f D →
      (∀ x ∈ D, divCoeffGrad A f x = 0) →
      MemLp f 2 ((volume : Measure R3).restrict D) →
      ∀ (c : R3), closedBall c (2 * d) ⊆ D →
      ∀ v : R3, ‖v‖ ≤ d / 2 →
        |f (c + v) - ∑ j ∈ Finset.range k, (Nat.factorial j : ℝ)⁻¹ *
          iteratedFDeriv ℝ j f c (fun _ : Fin j => v)| ≤
            CT * ‖v‖ ^ k * (eLpNorm f 2 ((volume : Measure R3).restrict D)).toReal) :
    let J_k : ℝ := max (JH ⟨k, Nat.lt_succ_self k⟩) ((Nat.factorial k : ℝ) * CT)
    let n0 : ℕ := 1 + Nat.ceil (2 * Real.sqrt 3 / d)
    let G_B : ℕ := Nat.ceil ((2 * B + 4) ^ 3)
    let M_k : ℕ := ∑ j ∈ Finset.range k, 3 ^ j
    let V_B : ℝ := ((volume : Measure R3) (ball (0 : R3) B)).toReal
    let Q_k : ℝ := Real.sqrt V_B * J_k * (Real.sqrt 3) ^ k / (Nat.factorial k : ℝ)
    let Cerror : ℝ := 1 + max ((n0 : ℝ) ^ k) Q_k
    ∀ n : ℕ, 1 ≤ n →
    ∃ T : H →L[ℝ] Lp ℝ 2 ((volume : Measure R3).restrict S),
      FiniteDimensional ℝ (LinearMap.range T.toLinearMap) ∧
      Module.finrank ℝ (LinearMap.range T.toLinearMap) ≤ G_B * n ^ 3 * M_k ∧
      ‖R - T‖ ≤ Cerror / ((n : ℝ) ^ k) ∧
      (n < n0 → T = 0) := by
  classical
  let J_k : ℝ := max (JH ⟨k, Nat.lt_succ_self k⟩) ((Nat.factorial k : ℝ) * CT)
  let n0 : ℕ := 1 + Nat.ceil (2 * Real.sqrt 3 / d)
  let G_B : ℕ := Nat.ceil ((2 * B + 4) ^ 3)
  let M_k : ℕ := ∑ j ∈ Finset.range k, 3 ^ j
  let V_B : ℝ := ((volume : Measure R3) (ball (0 : R3) B)).toReal
  let Q_k : ℝ := Real.sqrt V_B * J_k * (Real.sqrt 3) ^ k / (Nat.factorial k : ℝ)
  let Cerror : ℝ := 1 + max ((n0 : ℝ) ^ k) Q_k
  have hFac : 0 < (Nat.factorial k : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hJ_k : 0 < J_k := lt_of_lt_of_le (hJH ⟨k, Nat.lt_succ_self k⟩) (le_max_left _ _)
  have hCTLe : CT ≤ J_k / (Nat.factorial k : ℝ) :=
    (le_div_iff₀ hFac).mpr (by
      calc
        CT * (Nat.factorial k : ℝ) = (Nat.factorial k : ℝ) * CT := mul_comm _ _
        _ ≤ J_k := le_max_right _ _)
  have hQ : 0 ≤ Q_k := div_nonneg
    (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hJ_k.le)
      (pow_nonneg (Real.sqrt_nonneg _) _)) hFac.le
  have hCerror : 0 < Cerror := by
    have hm : 0 ≤ max ((n0 : ℝ) ^ k) Q_k := hQ.trans (le_max_right _ _)
    dsimp only [Cerror]
    linarith only [hm]
  let muD : Measure R3 := (volume : Measure R3).restrict D
  let muS : Measure R3 := (volume : Measure R3).restrict S
  let Y := Lp ℝ 2 muS
  -- C1.1: the canonical restriction and its derived finite-measure target.
  have hRNorm : ‖R‖ ≤ 1 := hR.1
  have hSB : S ⊆ ball (0 : R3) B := by
    intro x hx
    exact hDB (hSD hx)
  have hSFinite : (volume : Measure R3) S ≠ (∞ : ℝ≥0∞) :=
    ne_top_of_le_ne_top measure_ball_ne_top (measure_mono hSB)
  letI : IsFiniteMeasure muS := isFiniteMeasure_restrict.mpr hSFinite
  change ∀ n : ℕ, 1 ≤ n →
    ∃ T : H →L[ℝ] Y,
      FiniteDimensional ℝ (LinearMap.range T.toLinearMap) ∧
      Module.finrank ℝ (LinearMap.range T.toLinearMap) ≤ G_B * n ^ 3 * M_k ∧
      ‖R - T‖ ≤ Cerror / ((n : ℝ) ^ k) ∧ (n < n0 → T = 0)
  intro n hn
  have hN : 0 < (n : ℝ) := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hn
  have hNPow : 0 < (n : ℝ) ^ k := pow_pos hN k
  -- C1.2: the small-n branch uses the canonical restriction bound only.
  by_cases hSmallN : n < n0
  · refine ⟨0, ?_, ?_, ?_, fun _ => rfl⟩
    · change FiniteDimensional ℝ (LinearMap.range (0 : H →ₗ[ℝ] Y))
      rw [LinearMap.range_zero]
      infer_instance
    · change Module.finrank ℝ (LinearMap.range (0 : H →ₗ[ℝ] Y)) ≤ _
      rw [LinearMap.range_zero]
      simp
    · have hPower : (n : ℝ) ^ k ≤ (n0 : ℝ) ^ k :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hSmallN.le) k
      have hC : (n : ℝ) ^ k ≤ Cerror := by
        have hm := le_max_left ((n0 : ℝ) ^ k) Q_k
        dsimp only [Cerror]
        linarith only [hPower, hm]
      have hOne : 1 ≤ Cerror / ((n : ℝ) ^ k) :=
        (le_div_iff₀ hNPow).mpr (by simpa only [one_mul] using hC)
      simpa only [sub_zero] using hRNorm.trans hOne
  have hLarge : n0 ≤ n := Nat.le_of_not_gt hSmallN
  have hMesh : Real.sqrt 3 / (n : ℝ) ≤ d / 2 := by
    have hc : 2 * Real.sqrt 3 / d ≤ (Nat.ceil (2 * Real.sqrt 3 / d) : ℝ) := Nat.le_ceil _
    have hcn : (Nat.ceil (2 * Real.sqrt 3 / d) : ℝ) < (n : ℝ) := by
      exact_mod_cast (Nat.lt_of_lt_of_le (by omega : Nat.ceil (2 * Real.sqrt 3 / d) < n0) hLarge)
    have hm : 2 * Real.sqrt 3 < (n : ℝ) * d := (div_lt_iff₀ hd).mp (hc.trans_lt hcn)
    apply (div_le_iff₀ hN).mpr
    nlinarith only [hm]
  -- C1.2/C1.3: actual finite half-open cells and input-independent centers.
  let cell : (Fin 3 → ℤ) → Set R3 := fun nu =>
    S ∩ {x : R3 | ∀ r : Fin 3,
      (nu r : ℝ) / (n : ℝ) ≤ x r ∧ x r < ((nu r : ℝ) + 1) / (n : ℝ)}
  let grid : FiniteHarmonicCubePartition B n S D d := Classical.choice
    (nonempty_finite_harmonic_cube_partition B hB n hn S hS hSB D d hd hBuffer)
  let I := grid.indices
  let center : {nu : Fin 3 → ℤ // nu ∈ I} → R3 := grid.center
  have hCenter : ∀ nu : {nu : Fin 3 → ℤ // nu ∈ I}, center nu ∈ cell nu.val := grid.center_mem
  have hCover : S = ⋃ nu ∈ (I : Set (Fin 3 → ℤ)), cell nu := grid.cover
  have hDisjoint : ∀ nu ∈ I, ∀ mu ∈ I, nu ≠ mu → Disjoint (cell nu) (cell mu) := grid.disjoint
  have hMeasurable : ∀ nu : Fin 3 → ℤ, MeasurableSet (cell nu) := grid.measurable
  have hDiameter : ∀ nu ∈ I, ∀ x ∈ cell nu, ∀ y ∈ cell nu,
      dist x y ≤ Real.sqrt 3 / (n : ℝ) := grid.diameter
  have hCard : I.card ≤ G_B * n ^ 3 := grid.card_le
  have hCenterRoom : ∀ nu : {nu : Fin 3 → ℤ // nu ∈ I},
      closedBall (center nu) (2 * d) ⊆ D := grid.room
  -- C1.3: the dependent finite word labels have exactly I.card * M_k entries.
  let CellIndex := {nu : Fin 3 → ℤ // nu ∈ I}
  let WordIndex := Σ j : Fin k, (Fin j.val → Fin 3)
  let Label := CellIndex × WordIndex
  have hLabelCard : Fintype.card Label = I.card * M_k := by
    have hSum : (∑ j : Fin k, 3 ^ j.val) = M_k :=
      (Finset.sum_range (fun j : ℕ => 3 ^ j)).symm
    simp only [Label, Fintype.card_prod, CellIndex, Fintype.card_coe,
      WordIndex, Fintype.card_sigma, Fintype.card_pi_const, Fintype.card_fin]
    rw [hSum]
  -- C1.4: the actual fixed measurable indicator-polynomial output family.
  let p : Label → R3 → ℝ := fun beta x =>
    (Nat.factorial beta.2.1.val : ℝ)⁻¹ *
      ∏ r : Fin beta.2.1.val, (x - center beta.1) (beta.2.2 r)
  let g : Label → R3 → ℝ := fun beta => (cell beta.1.val).indicator (p beta)
  have hp (beta : Label) : Continuous (p beta) := by
    apply continuous_const.mul
    apply continuous_finsetProd Finset.univ
    intro r _hr
    exact (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) (beta.2.2 r)).comp
      (continuous_id.sub continuous_const)
  have hCoordinate (beta : Label) (x : R3) (hx : x ∈ cell beta.1.val)
      (r : Fin beta.2.1.val) : |(x - center beta.1) (beta.2.2 r)| ≤ 1 / (n : ℝ) := by
    have hc := hCenter beta.1
    have hxLo := (hx.2 (beta.2.2 r)).1
    have hxHi := (hx.2 (beta.2.2 r)).2
    have hcLo := (hc.2 (beta.2.2 r)).1
    have hcHi := (hc.2 (beta.2.2 r)).2
    have hLength : ((beta.1.val (beta.2.2 r) : ℝ) + 1) / (n : ℝ) -
        (beta.1.val (beta.2.2 r) : ℝ) / (n : ℝ) = 1 / (n : ℝ) := by ring
    rw [PiLp.sub_apply]
    apply abs_le.mpr
    constructor <;> linarith only [hxLo, hxHi, hcLo, hcHi, hLength]
  have hgBound (beta : Label) (x : R3) :
      ‖g beta x‖ ≤ (1 / (n : ℝ)) ^ beta.2.1.val /
        (Nat.factorial beta.2.1.val : ℝ) := by
    have hfac : 0 < (Nat.factorial beta.2.1.val : ℝ) := by
      exact_mod_cast Nat.factorial_pos beta.2.1.val
    by_cases hx : x ∈ cell beta.1.val
    · have hProd : |∏ r : Fin beta.2.1.val, (x - center beta.1) (beta.2.2 r)| ≤
          (1 / (n : ℝ)) ^ beta.2.1.val := by
        calc
          _ = ∏ r : Fin beta.2.1.val, |(x - center beta.1) (beta.2.2 r)| :=
            Finset.abs_prod _ _
          _ ≤ ∏ _r : Fin beta.2.1.val, (1 / (n : ℝ)) :=
            Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun r _ => hCoordinate beta x hx r)
          _ = _ := by simp
      have hb := mul_le_mul_of_nonneg_left hProd (inv_nonneg.mpr hfac.le)
      simpa only [g, Set.indicator_of_mem hx, p, Real.norm_eq_abs, abs_mul,
        abs_inv, abs_of_pos hfac, div_eq_mul_inv, mul_comm] using hb
    · change ‖(cell beta.1.val).indicator (p beta) x‖ ≤ _
      rw [Set.indicator_of_notMem hx, norm_zero]
      exact div_nonneg (pow_nonneg (div_nonneg zero_le_one hN.le) _) hfac.le
  have hgMem (beta : Label) : MemLp (g beta) 2 muS :=
    MemLp.of_bound ((hp beta).stronglyMeasurable.indicator
      (hMeasurable beta.1.val)).aestronglyMeasurable
      ((1 / (n : ℝ)) ^ beta.2.1.val / (Nat.factorial beta.2.1.val : ℝ))
      (Filter.Eventually.of_forall (hgBound beta))
  let b : Label → Y := fun beta => (hgMem beta).toLp (g beta)
  -- C1.5: all ordered coordinate words, including the unique order-zero word.
  -- C1.6: actual H0 scalar jet maps, then bounded extensions to the SAME H.
  have hEll (beta : Label) : ∃ ell : S0 →L[ℝ] ℝ,
      ‖ell‖ ≤ JH beta.2.1.castSucc ∧
      ∀ (u : S0) (f : R3 → ℝ), ContDiffOn ℝ ∞ f D →
        (∀ x ∈ D, divCoeffGrad A f x = 0) →
        ∀ hf : MemLp f 2 muD, hf.toLp f = (u : Lp ℝ 2 muD) →
        ell u = iteratedFDeriv ℝ beta.2.1.val f (center beta.1)
          (fun r => EuclideanSpace.single (beta.2.2 r) (1 : ℝ)) := by
    have hc : closedBall (center beta.1) d ⊆ D :=
      (closedBall_subset_closedBall (by linarith only [hd] : d ≤ 2 * d)).trans
        (hCenterRoom beta.1)
    exact hJetEval beta.2.1.castSucc (center beta.1) hc beta.2.2
  choose ell hEllNorm hEllAgree using hEll
  have hEllBound (beta : Label) (u : S0) :
      ‖ell beta u‖ ≤ JH beta.2.1.castSucc * ‖e u‖ := by
    calc
      _ ≤ ‖ell beta‖ * ‖u‖ := (ell beta).le_opNorm u
      _ ≤ JH beta.2.1.castSucc * ‖u‖ := mul_le_mul_of_nonneg_right (hEllNorm beta) (norm_nonneg u)
      _ = _ := by rw [e.norm_map]
  have hExtensions (beta : Label) : ∃ L : H →L[ℝ] ℝ,
      ‖L‖ ≤ JH beta.2.1.castSucc ∧ ∀ u : S0, L (e u) = ell beta u := by
    refine ⟨(ell beta).toLinearMap.extendOfNorm e.toLinearMap,
      LinearMap.opNorm_extendOfNorm_le he (hJH beta.2.1.castSucc).le (hEllBound beta), ?_⟩
    intro u
    exact LinearMap.extendOfNorm_eq he ⟨JH beta.2.1.castSucc, hEllBound beta⟩ u
  choose lbar _hLbarNorm hLbarAgree using hExtensions
  -- C1.7: fixed finite Lp output vectors and a proved finite-dimensional range.
  let T : H →L[ℝ] Y := ∑ beta : Label, (lbar beta).smulRight (b beta)
  have hSynthesis := finite_rank_synthesis lbar b
  have hTFinite : FiniteDimensional ℝ (LinearMap.range T.toLinearMap) := hSynthesis.1
  have hRank : Module.finrank ℝ (LinearMap.range T.toLinearMap) ≤ G_B * n ^ 3 * M_k := by
    calc
      _ ≤ Fintype.card Label := hSynthesis.2
      _ = I.card * M_k := hLabelCard
      _ ≤ _ := Nat.mul_le_mul_right M_k hCard
  -- C1.8: AE class formulas, with no pointwise quotient-class identification.
  have hTClass (u : S0) : (T (e u) : R3 → ℝ) =ᵐ[muS]
      (fun x => ∑ beta : Label, ell beta u * g beta x) := by
    have hTValue : T (e u) = ∑ beta : Label, lbar beta (e u) • b beta := by
      simp only [T, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply]
    rw [hTValue]
    simpa only [b, hLbarAgree] using
      finite_sum_smul_toLp_ae muS g hgMem (fun beta : Label => lbar beta (e u))
  let A_n : ℝ := J_k / (Nat.factorial k : ℝ) * (Real.sqrt 3 / (n : ℝ)) ^ k
  have hAn : 0 ≤ A_n := mul_nonneg (div_nonneg hJ_k.le hFac.le)
    (pow_nonneg (div_nonneg (Real.sqrt_nonneg _) hN.le) _)
  have hDenseError (u : S0) : ‖(R - T) (e u)‖ ≤ Q_k / ((n : ℝ) ^ k) * ‖e u‖ := by
    let repExists := (hRaw (u : Lp ℝ 2 muD)).mp u.property
    let f : R3 → ℝ := Classical.choose repExists
    have hf : ContDiffOn ℝ ∞ f D := (Classical.choose_spec repExists).1
    have hpde : ∀ x ∈ D, divCoeffGrad A f x = 0 := (Classical.choose_spec repExists).2.1
    have hAE : ((u : Lp ℝ 2 muD) : R3 → ℝ) =ᵐ[muD] f :=
      (Classical.choose_spec repExists).2.2
    have hfMem : MemLp f 2 muD := MemLp.ae_eq hAE (Lp.memLp (u : Lp ℝ 2 muD))
    have hfClass : hfMem.toLp f = (u : Lp ℝ 2 muD) :=
      Lp.ext (hfMem.coeFn_toLp.trans hAE.symm)
    have hfClassE : hfMem.toLp f = (e u : Lp ℝ 2 muD) := hfClass.trans (hAmbient u).symm
    have hNorm : ‖e u‖ = (eLpNorm f 2 muD).toReal := by
      calc
        _ = ‖u‖ := e.norm_map u
        _ = ‖(u : Lp ℝ 2 muD)‖ := rfl
        _ = ‖hfMem.toLp f‖ := congrArg norm hfClass.symm
        _ = _ := Lp.norm_toLp f hfMem
    have hPoint (x : R3) (hx : x ∈ S) :
        |f x - ∑ beta : Label, ell beta u * g beta x| ≤ A_n * ‖e u‖ := by
      have hTaylorPure :
          ∀ (nu : {nu : Fin 3 → ℤ // nu ∈ grid.indices}) (v : R3),
            ‖v‖ ≤ d / 2 →
            |f (grid.center nu + v) -
                ∑ j ∈ Finset.range k, (Nat.factorial j : ℝ)⁻¹ *
                  iteratedFDeriv ℝ j f (grid.center nu) (fun _ : Fin j => v)| ≤
              CT * ‖v‖ ^ k * ‖e u‖ := by
        intro nu v hv
        have ht := hTaylorBound f hf hpde hfMem
          (grid.center nu) (grid.room nu) v hv
        rw [← hNorm] at ht
        exact ht
      have hPure := abs_sub_sum_indicator_taylor_le
        B n hn S D d grid k hMesh f
        (fun beta => ell beta u)
        (fun beta => hEllAgree beta u f hf hpde hfMem hfClass)
        CT hCT.le ‖e u‖ (norm_nonneg _) hTaylorPure x hx
      -- The existing g, p, cell, center, I and Label are definitionally
      -- the literal indicator-polynomial family appearing in hPure.
      change |f x - ∑ beta : Label, ell beta u * g beta x| ≤
        CT * (Real.sqrt 3 / (n : ℝ)) ^ k * ‖e u‖ at hPure
      calc
        _ ≤ CT * (Real.sqrt 3 / (n : ℝ)) ^ k * ‖e u‖ := hPure
        _ ≤ (J_k / (Nat.factorial k : ℝ)) *
              (Real.sqrt 3 / (n : ℝ)) ^ k * ‖e u‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hCTLe
              (pow_nonneg (div_nonneg (Real.sqrt_nonneg _) hN.le) k))
            (norm_nonneg _)
        _ = A_n * ‖e u‖ := rfl
    have hRClass : (R (e u) : R3 → ℝ) =ᵐ[muS] f :=
      hR.2 (e u) f hf hpde hfMem hfClassE
    let z : Y := (R - T) (e u)
    have hzClass : (z : R3 → ℝ) =ᵐ[muS]
        (fun x => f x - ∑ beta : Label, ell beta u * g beta x) := by
      filter_upwards [Lp.coeFn_sub (R (e u)) (T (e u)), hRClass, hTClass u] with x hsub hr ht
      exact hsub.trans (congrArg₂ (fun q r : ℝ => q - r) hr ht)
    have hzBound : ∀ᵐ x ∂muS, |z x| ≤ A_n * ‖e u‖ := by
      filter_upwards [hzClass, ae_restrict_mem hS.measurableSet] with x hz hxS
      rw [hz]
      exact hPoint x hxS
    -- C1.9: square integration in exactly the original restricted scalar L2 norm.
    have hCap : 0 ≤ A_n * ‖e u‖ := mul_nonneg hAn (norm_nonneg _)
    have hRoot : ‖z‖ ≤ Real.sqrt (((volume : Measure R3) S).toReal) * A_n * ‖e u‖ := by
      simpa only [muS, Measure.restrict_apply_univ, mul_assoc] using
        l2_norm_le_sqrt_measure_mul_of_ae_bound muS z (A_n * ‖e u‖) hCap hzBound
    have hVolume : ((volume : Measure R3) S).toReal ≤ V_B :=
      ENNReal.toReal_mono measure_ball_ne_top (measure_mono hSB)
    calc
      ‖(R - T) (e u)‖ = ‖z‖ := rfl
      _ ≤ Real.sqrt (((volume : Measure R3) S).toReal) * A_n * ‖e u‖ := hRoot
      _ ≤ Real.sqrt V_B * A_n * ‖e u‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (Real.sqrt_le_sqrt hVolume) hAn) (norm_nonneg _)
      _ = Q_k / ((n : ℝ) ^ k) * ‖e u‖ := by
        dsimp only [A_n, Q_k]
        rw [div_pow]
        ring
  -- C1.9: density extends ONLY the continuous error inequality, not regularity.
  have hAllError (w : H) : ‖(R - T) w‖ ≤ Q_k / ((n : ℝ) ^ k) * ‖w‖ := by
    exact he.induction_on w
      (isClosed_le (R - T).continuous.norm (continuous_const.mul continuous_norm)) hDenseError
  have hOp : ‖R - T‖ ≤ Q_k / ((n : ℝ) ^ k) :=
    (R - T).opNorm_le_bound (div_nonneg hQ hNPow.le) hAllError
  have hQC : Q_k ≤ Cerror := by
    have hm := le_max_right ((n0 : ℝ) ^ k) Q_k
    dsimp only [Cerror]
    linarith only [hm]
  refine ⟨T, hTFinite, hRank, hOp.trans (div_le_div_of_nonneg_right hQC hNPow.le), ?_⟩
  intro hSmall
  exact False.elim (hSmallN hSmall)


theorem exists_uniform_dilated_metric_harmonic_compact_jets_and_finite_rank_restriction
    (a : Fin 2 → MatrixField) (ha : ∀ i : Fin 2, IsAdmissibleMetric (a i))
    (B : ℝ) (hB : 0 < B) (r_ext : ℝ) (hr_ext : 0 < r_ext) :
    ∃ lambda0 : ℝ, 0 < lambda0 ∧ lambda0 ≤ 1 ∧
      lambda0 * B < min r_ext (5 / 4 : ℝ) ∧
      (∀ (i : Fin 2) (m : ℕ) (d : ℝ), 0 < d →
        ∃ J : ℝ, 0 < J ∧
        ∀ lambda : ℝ, lambda ∈ Icc (0 : ℝ) lambda0 →
        ∀ (D : Set R3) (hD : IsOpen D), D ⊆ ball (0 : R3) B →
        let A : MatrixField := principalCoefficient (fun y : R3 => a i (lambda • y))
        let hA : ContDiffOn ℝ ∞ A D :=
          ((contDiff_principalCoefficient (a i) (ha i)).comp
            (contDiff_const_smul lambda)).contDiffOn
        let H := classicalHarmonicL2Space D hD A hA
        ∀ K : Compacts R3, (∀ x ∈ (K : Set R3), closedBall x d ⊆ D) →
        letI : CompactSpace K := TopologicalSpace.Compacts.instCompactSpaceSubtypeMem K
        letI : SeminormedAddCommGroup (ContinuousMultilinearMap ℝ (fun _ : Fin m => R3) ℝ) :=
          ContinuousMultilinearMap.seminormedAddCommGroup (𝕜 := ℝ)
            (E := fun _ : Fin m => R3) (G := ℝ)
        letI : NormedSpace ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin m => R3) ℝ) :=
          ContinuousMultilinearMap.normedSpace (𝕜 := ℝ) (𝕜' := ℝ)
            (E := fun _ : Fin m => R3) (G := ℝ)
        letI : SeminormedAddCommGroup C(K, ContinuousMultilinearMap ℝ (fun _ : Fin m => R3) ℝ) :=
          ContinuousMap.instSeminormedAddCommGroup
        letI : NormedSpace ℝ C(K, ContinuousMultilinearMap ℝ (fun _ : Fin m => R3) ℝ) := ContinuousMap.normedSpace
        letI : NormedSpace ℝ H := ClosedSubmodule.normedSpace H
        ∃ E : H →L[ℝ] C(K, ContinuousMultilinearMap ℝ (fun _ : Fin m => R3) ℝ),
          ‖E‖ ≤ J ∧
          ∀ (w : H) (f : R3 → ℝ), ContDiffOn ℝ ∞ f D →
            (∀ x ∈ D, divCoeffGrad A f x = 0) →
            ∀ hf : MemLp f 2 ((volume : Measure R3).restrict D),
              hf.toLp f = (w : Lp ℝ 2 ((volume : Measure R3).restrict D)) →
              ∀ x : K, E w x = iteratedFDeriv ℝ m f (x : R3)) ∧
      ∀ (i : Fin 2) (k : ℕ), 1 ≤ k → ∀ d : ℝ, 0 < d →
      ∃ JH : Fin (k + 1) → ℝ, (∀ j : Fin (k + 1), 0 < JH j) ∧
      ∃ CT : ℝ, 0 < CT ∧
      let J_k : ℝ := max (JH ⟨k, Nat.lt_succ_self k⟩) ((Nat.factorial k : ℝ) * CT)
      let n0 : ℕ := 1 + Nat.ceil (2 * Real.sqrt 3 / d)
      let G_B : ℕ := Nat.ceil ((2 * B + 4) ^ 3)
      let M_k : ℕ := ∑ j ∈ Finset.range k, 3 ^ j
      let V_B : ℝ := ((volume : Measure R3) (ball (0 : R3) B)).toReal
      let Q_k : ℝ := Real.sqrt V_B * J_k * (Real.sqrt 3) ^ k / (Nat.factorial k : ℝ)
      let Cerror : ℝ := 1 + max ((n0 : ℝ) ^ k) Q_k
      0 < Cerror ∧
      ∀ lambda : ℝ, lambda ∈ Icc (0 : ℝ) lambda0 →
      ∀ (D : Set R3) (hD : IsOpen D), D ⊆ ball (0 : R3) B →
      let A : MatrixField := principalCoefficient (fun y : R3 => a i (lambda • y))
      let hA : ContDiffOn ℝ ∞ A D :=
        ((contDiff_principalCoefficient (a i) (ha i)).comp
          (contDiff_const_smul lambda)).contDiffOn
      let H := classicalHarmonicL2Space D hD A hA
      ∀ (S : Set R3) (hS : IsOpen S), S.Nonempty → IsCompact (closure S) →
      (∀ x ∈ closure S, closedBall x (2 * d) ⊆ D) →
      ∀ hSD : S ⊆ D,
      let R : H →L[ℝ] Lp ℝ 2 ((volume : Measure R3).restrict S) :=
        (Lp.LpToLpOfMeasureLeSMul (by simp : (1 : ℝ≥0∞) ≠ ⊤)
          (show (volume : Measure R3).restrict S ≤
            (1 : ℝ≥0∞) • (volume : Measure R3).restrict D from
            by simpa only [one_smul] using Measure.restrict_mono_set volume hSD)).comp
          H.toSubmodule.subtypeL
      ‖R‖ ≤ 1 ∧
      ∀ n : ℕ, 1 ≤ n →
      ∃ T : H →L[ℝ] Lp ℝ 2 ((volume : Measure R3).restrict S),
        FiniteDimensional ℝ (LinearMap.range T.toLinearMap) ∧
        Module.finrank ℝ (LinearMap.range T.toLinearMap) ≤ G_B * n ^ 3 * M_k ∧
        ‖R - T‖ ≤ Cerror / ((n : ℝ) ^ k) ∧
        (n < n0 → T = 0) := by
  classical
  -- C1.0: all producer cutoffs precede every order, buffer and domain.
  choose lambdaO hLambdaO _hLambdaOOne hJet using
    (fun i : Fin 2 =>
      exists_uniform_dilated_metric_harmonic_compact_jet_maps (a i) (ha i) B hB)
  choose lambdaH hLambdaH _hLambdaHOne hEval using
    (fun i : Fin 2 =>
      exists_uniform_dilated_metric_classical_harmonic_jet_evaluations (a i) (ha i) B hB)
  choose lambdaT hLambdaT _hLambdaTOne hTaylor using
    (fun i : Fin 2 =>
      exists_uniform_dilated_metric_buffered_taylor_remainder_bound (a i) (ha i) B hB)
  let eps : Fin 2 → ℝ := fun i => min (lambdaO i) (min (lambdaH i) (lambdaT i))
  have hEps (i : Fin 2) : 0 < eps i :=
    lt_min (hLambdaO i) (lt_min (hLambdaH i) (hLambdaT i))
  let lambda0 : ℝ := min (min (eps 0) (eps 1))
    (min 1 (min (1 / (B + 1)) (r_ext / (2 * (B + 1)))))
  have hBp : 0 < B + 1 := by linarith only [hB]
  have hLambda0 : 0 < lambda0 :=
    lt_min (lt_min (hEps 0) (hEps 1))
      (lt_min zero_lt_one (lt_min (div_pos zero_lt_one hBp)
        (div_pos hr_ext (mul_pos (by norm_num) hBp))))
  have hLambda0One : lambda0 ≤ 1 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hPair (f : Fin 2 → ℝ) (h0 : lambda0 ≤ f 0) (h1 : lambda0 ≤ f 1) :
      ∀ i : Fin 2, lambda0 ≤ f i := by
    intro i
    refine Fin.cases h0 ?_ i
    intro j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact h1
  have hLambdaEps : ∀ i : Fin 2, lambda0 ≤ eps i :=
    hPair eps ((min_le_left _ _).trans (min_le_left _ _))
      ((min_le_left _ _).trans (min_le_right _ _))
  have hStripO (i : Fin 2) {lambda : ℝ} (hl : lambda ∈ Icc (0 : ℝ) lambda0) :
      lambda ∈ Icc (0 : ℝ) (lambdaO i) :=
    ⟨hl.1, hl.2.trans ((hLambdaEps i).trans (min_le_left _ _))⟩
  have hStripH (i : Fin 2) {lambda : ℝ} (hl : lambda ∈ Icc (0 : ℝ) lambda0) :
      lambda ∈ Icc (0 : ℝ) (lambdaH i) :=
    ⟨hl.1, hl.2.trans ((hLambdaEps i).trans
      ((min_le_right _ _).trans (min_le_left _ _)))⟩
  have hStripT (i : Fin 2) {lambda : ℝ} (hl : lambda ∈ Icc (0 : ℝ) lambda0) :
      lambda ∈ Icc (0 : ℝ) (lambdaT i) :=
    ⟨hl.1, hl.2.trans ((hLambdaEps i).trans
      ((min_le_right _ _).trans (min_le_right _ _)))⟩
  have hSmall : lambda0 ≤ 1 / (B + 1) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hExt : lambda0 ≤ r_ext / (2 * (B + 1)) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hLambdaB : lambda0 * B < min r_ext (5 / 4 : ℝ) := by
    have h1 : lambda0 * (B + 1) ≤ 1 := (le_div_iff₀ hBp).mp hSmall
    have h2 : lambda0 * (2 * (B + 1)) ≤ r_ext :=
      (le_div_iff₀ (mul_pos (by norm_num) hBp)).mp hExt
    have hp : 0 < lambda0 * B := mul_pos hLambda0 hB
    apply lt_min
    · nlinarith only [h2, hLambda0, hp]
    · nlinarith only [h1, hLambda0]
  refine ⟨lambda0, hLambda0, hLambda0One, hLambdaB, ?_, ?_⟩
  -- C1.10: the entire compact-jet conjunct on the actual closed H.
  · intro i m d hd
    obtain ⟨J, hJ, hBound⟩ := hJet i m d hd
    refine ⟨J, hJ, ?_⟩
    intro lambda hLambda D hD hDB
    exact hBound lambda (hStripO i hLambda) D hD hDB
  -- C1.0/C1.6: finite jet witnesses and Taylor cap before lambda,D,S,n.
  · intro i k hk d hd
    choose JH hJH hJetEval using (fun j : Fin (k + 1) => hEval i j.val d hd)
    have hTaylorForOrder :
        ∃ CT : ℝ, 0 < CT ∧
        ∀ lambda : ℝ, lambda ∈ Icc (0 : ℝ) (lambdaT i) →
        ∀ D : Set R3, IsOpen D → D ⊆ ball (0 : R3) B →
        ∀ f : R3 → ℝ, ContDiffOn ℝ ∞ f D →
        (∀ x ∈ D,
          divCoeffGrad (principalCoefficient (fun y : R3 => a i (lambda • y))) f x = 0) →
        MemLp f 2 ((volume : Measure R3).restrict D) →
        ∀ c : R3, closedBall c (2 * d) ⊆ D →
        ∀ v : R3, ‖v‖ ≤ d / 2 →
          |f (c + v) -
            ∑ j ∈ Finset.range k, ((Nat.factorial j : ℕ) : ℝ)⁻¹ *
              iteratedFDeriv ℝ j f c (fun _ : Fin j => v)| ≤
            CT * ‖v‖ ^ k * (eLpNorm f 2 ((volume : Measure R3).restrict D)).toReal :=
      hTaylor i k hk d hd
    obtain ⟨CT, hCT, hTaylorBound⟩ := hTaylorForOrder
    refine ⟨JH, hJH, CT, hCT, ?_⟩
    let J_k : ℝ := max (JH ⟨k, Nat.lt_succ_self k⟩) ((Nat.factorial k : ℝ) * CT)
    let n0 : ℕ := 1 + Nat.ceil (2 * Real.sqrt 3 / d)
    let G_B : ℕ := Nat.ceil ((2 * B + 4) ^ 3)
    let M_k : ℕ := ∑ j ∈ Finset.range k, 3 ^ j
    let V_B : ℝ := ((volume : Measure R3) (ball (0 : R3) B)).toReal
    let Q_k : ℝ := Real.sqrt V_B * J_k * (Real.sqrt 3) ^ k / (Nat.factorial k : ℝ)
    let Cerror : ℝ := 1 + max ((n0 : ℝ) ^ k) Q_k
    have hFac : 0 < (Nat.factorial k : ℝ) := by exact_mod_cast Nat.factorial_pos k
    have hJ_k : 0 < J_k := lt_of_lt_of_le (hJH ⟨k, Nat.lt_succ_self k⟩) (le_max_left _ _)
    have hCTLe : CT ≤ J_k / (Nat.factorial k : ℝ) :=
      (le_div_iff₀ hFac).mpr (by
        calc
          CT * (Nat.factorial k : ℝ) = (Nat.factorial k : ℝ) * CT := mul_comm _ _
          _ ≤ J_k := le_max_right _ _)
    have hQ : 0 ≤ Q_k := div_nonneg
      (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hJ_k.le)
        (pow_nonneg (Real.sqrt_nonneg _) _)) hFac.le
    have hCerror : 0 < Cerror := by
      have hm : 0 ≤ max ((n0 : ℝ) ^ k) Q_k := hQ.trans (le_max_right _ _)
      dsimp only [Cerror]
      linarith only [hm]
    change 0 < Cerror ∧ _
    refine ⟨hCerror, ?_⟩
    intro lambda hLambda D hD hDB A hA H S hS hSne hCompactS hBuffer hSD R
    let muD : Measure R3 := (volume : Measure R3).restrict D
    let muS : Measure R3 := (volume : Measure R3).restrict S
    let Y := Lp ℝ 2 muS
    let S0 := classicalDilatedMetricHarmonicL2Submodule (a i) (ha i) lambda D hD
    have hC0 := classicalDilatedMetricHarmonicL2Submodule_closure_and_representatives
      (a i) (ha i) lambda D hD
    have hRaw : ∀ u : Lp ℝ 2 muD,
        u ∈ S0 ↔ ∃ f : R3 → ℝ, ContDiffOn ℝ ∞ f D ∧
          (∀ x ∈ D, divCoeffGrad A f x = 0) ∧
          (u : R3 → ℝ) =ᵐ[muD] f := by
      exact hC0.1
    have hClosure : S0.closure = H := hC0.2.1
    have hSH : (S0 : Set (Lp ℝ 2 muD)) ⊆ (H : Set (Lp ℝ 2 muD)) := by
      intro u hu
      rw [← hClosure]
      exact S0.le_topologicalClosure hu
    let e : S0 →ₗᵢ[ℝ] H :=
      { toFun := fun v => ⟨(v : Lp ℝ 2 muD), hSH v.property⟩
        map_add' := by intro v w; rfl
        map_smul' := by intro r v; rfl
        norm_map' := by intro v; rfl }
    have he : DenseRange e := by
      change DenseRange (Set.inclusion hSH)
      apply (denseRange_inclusion_iff hSH).mpr
      rw [← hClosure]
      exact Set.Subset.rfl
    have hAmbient (u : S0) : (e u : Lp ℝ 2 muD) = (u : Lp ℝ 2 muD) := rfl
    have hR : ‖R‖ ≤ 1 ∧
        ∀ (w : H) (f : R3 → ℝ), ContDiffOn ℝ ∞ f D →
          (∀ x ∈ D, divCoeffGrad A f x = 0) →
          ∀ hf : MemLp f 2 muD, hf.toLp f = (w : Lp ℝ 2 muD) →
            (R w : R3 → ℝ) =ᵐ[muS] f := by
      exact hC0.2.2.2.2.2 S hS hSD
    refine ⟨hR.1, ?_⟩
    refine exists_finite_rank_restriction_of_jet_taylor B hB k hk d hd D hD hDB A H S0
      JH hJH CT hCT e he hAmbient hRaw S hS hBuffer hSD R hR ?_ ?_
    · intro j c hc alpha
      obtain ⟨E, ell, _hE, hEllNorm, hEllValue, hAgree⟩ :=
        hJetEval j lambda (hStripH i hLambda) D hD hDB c hc
      refine ⟨ell alpha, hEllNorm alpha, ?_⟩
      intro u f hf hpde hfMem hfClass
      rw [hEllValue, hAgree u f hf hpde hfMem hfClass]
    · exact hTaylorBound lambda (hStripT i hLambda) D hD hDB

end OAI.AnisotropicCalderon.Regularity

#print axioms OAI.AnisotropicCalderon.Regularity.exists_uniform_dilated_metric_harmonic_compact_jets_and_finite_rank_restriction
