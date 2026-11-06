import Calderon.ClassicalHarmonicL2Closure
import Mathlib.Topology.Algebra.Module.ClosedSubmodule

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory Filter TopologicalSpace
open scoped ContDiff Topology Matrix.Norms.Elementwise ENNReal Classical
namespace OAI.AnisotropicCalderon.Regularity
open EnergyBridge

noncomputable def classicalHarmonicL2Space
    (D : Set R3) (hD : IsOpen D)
    (A : R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (hA : ContDiffOn ℝ ∞ A D) :
    ClosedSubmodule ℝ (Lp ℝ 2 ((volume : Measure R3).restrict D))
 := by
  classical
  let μ : Measure R3 := (volume : Measure R3).restrict D
  let H0 : Submodule ℝ (Lp ℝ 2 μ) :=
    { carrier := {v | ∃ U : R3 → ℝ, ContDiffOn ℝ ∞ U D ∧
        (∀ x ∈ D, divCoeffGrad A U x = 0) ∧ (v : R3 → ℝ) =ᵐ[μ] U}
      zero_mem' := by
        refine ⟨fun _ => 0, contDiffOn_const, ?_, ?_⟩
        · intro x hx
          have hAx : DifferentiableAt ℝ A x :=
            (hA.contDiffAt (hD.mem_nhds hx)).differentiableAt (by simp)
          have hZ : ContDiffAt ℝ 2 (fun _ : R3 => (0 : ℝ)) x := contDiffAt_const
          have he := Jets.divCoeffGrad_smul (A := A) (u := fun _ : R3 => (0 : ℝ))
            (x := x) 0 hAx hZ
          have he0 : divCoeffGrad A (0 : R3 → ℝ) x = 0 := by
            simpa only [zero_smul, zero_mul] using he
          have hfun : (0 : R3 → ℝ) = (fun _ => 0) := by
            funext t
            rfl
          exact (congrArg (fun u : R3 → ℝ => divCoeffGrad A u x) hfun).symm.trans he0
        · exact Lp.coeFn_zero ℝ 2 μ
      add_mem' := by
        intro u v hu hv
        obtain ⟨U, hU, hUP, huU⟩ := hu
        obtain ⟨V, hV, hVP, hvV⟩ := hv
        refine ⟨U+V, hU.add hV, ?_, ?_⟩
        · intro x hx
          have hAx : DifferentiableAt ℝ A x :=
            (hA.contDiffAt (hD.mem_nhds hx)).differentiableAt (by simp)
          have he := Jets.divCoeffGrad_add hAx
            ((hU.contDiffAt (hD.mem_nhds hx)).of_le (by simp))
            ((hV.contDiffAt (hD.mem_nhds hx)).of_le (by simp))
          rw [he, hUP x hx, hVP x hx, add_zero]
        · filter_upwards [Lp.coeFn_add u v, huU, hvV] with x huv hxU hxV
          exact huv.trans ((congrArg (fun a : ℝ => a+v x) hxU).trans
            (congrArg (fun b : ℝ => U x+b) hxV))
      smul_mem' := by
        intro c u hu
        obtain ⟨U, hU, hUP, huU⟩ := hu
        refine ⟨c • U, hU.const_smul c, ?_, ?_⟩
        · intro x hx
          have hAx : DifferentiableAt ℝ A x :=
            (hA.contDiffAt (hD.mem_nhds hx)).differentiableAt (by simp)
          rw [Jets.divCoeffGrad_smul c hAx
            ((hU.contDiffAt (hD.mem_nhds hx)).of_le (by simp)), hUP x hx, mul_zero]
        · filter_upwards [Lp.coeFn_smul c u, huU] with x hcu hxU
          exact hcu.trans (congrArg (fun a : ℝ => c • a) hxU) }
  exact H0.closure

theorem injective_restrict_classicalHarmonicL2Space
    (D : Set R3) (hD : IsOpen D) (hconn : IsConnected D)
    (A : R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (hA : ContDiffOn ℝ ∞ A D) (hpos : ∀ x ∈ D, (A x).PosDef)
    (S : Set R3) (hS : IsOpen S) (hSne : S.Nonempty) (hSD : S ⊆ D) :
    let E := classicalHarmonicL2Space D hD A hA
    let R : E →L[ℝ] Lp ℝ 2 ((volume : Measure R3).restrict S) :=
      (Lp.LpToLpOfMeasureLeSMul (by simp : (1 : ℝ≥0∞) ≠ ⊤)
        (show (volume : Measure R3).restrict S ≤
          (1 : ℝ≥0∞) • (volume : Measure R3).restrict D from
          by simpa only [one_smul] using Measure.restrict_mono_set volume hSD)).comp
        E.toSubmodule.subtypeL
    Function.Injective R
 := by
  classical
  intro E R u v huv
  let w : E := u-v
  have hRw : R w = 0 := by
    change R (u-v) = 0
    rw [map_sub, huv, sub_self]
  have hwClosure : (w : Lp ℝ 2 ((volume : Measure R3).restrict D)) ∈
      closure {v : Lp ℝ 2 ((volume : Measure R3).restrict D) | ∃ U : R3 → ℝ,
        ContDiffOn ℝ ∞ U D ∧ (∀ x ∈ D, divCoeffGrad A U x = 0) ∧
          (v : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict D] U} := by
    exact w.property
  obtain ⟨U, hU, hUw, hUP⟩ :=
    exists_contDiffOn_representative_of_mem_closure_L2_classical_harmonics
      D hD A hA hpos (w : Lp ℝ 2 ((volume : Measure R3).restrict D)) hwClosure
  have hRestr : (volume : Measure R3).restrict S ≤
      (1 : ℝ≥0∞) • (volume : Measure R3).restrict D := by
    simpa only [one_smul] using Measure.restrict_mono_set volume hSD
  have hRval : (R w : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict S]
      (w : Lp ℝ 2 ((volume : Measure R3).restrict D)) := by
    exact Lp.coeFn_LpToLpOfMeasureLeSMul (by simp : (1 : ℝ≥0∞) ≠ ⊤)
      hRestr (w : Lp ℝ 2 ((volume : Measure R3).restrict D))
  have hRzero : (R w : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict S] (0 : R3 → ℝ) := by
    rw [hRw]
    exact Lp.coeFn_zero ℝ 2 ((volume : Measure R3).restrict S)
  have hUS : U =ᵐ[(volume : Measure R3).restrict S] (0 : R3 → ℝ) := by
    have hUwS : U =ᵐ[(volume : Measure R3).restrict S]
        (w : Lp ℝ 2 ((volume : Measure R3).restrict D)) :=
      ae_restrict_of_ae_restrict_of_subset (s := S) hSD hUw
    filter_upwards [hUwS, hRval, hRzero] with x hxU hxR hx0
    exact hxU.trans (hxR.symm.trans hx0)
  have hUSpoint : ∀ x ∈ S, U x = 0 := by
    intro x hx
    exact Measure.eqOn_open_of_ae_eq hUS hS (hU.continuousOn.mono hSD)
      continuousOn_const hx
  have hUD : ∀ x ∈ D, U x = 0 :=
    UCP.uniqueContinuation_aux D hD hconn A hA hpos U hU hUP S hS hSne hSD hUSpoint
  have hwzero : (w : Lp ℝ 2 ((volume : Measure R3).restrict D)) = 0 := by
    apply Lp.ext
    filter_upwards [hUw, ae_restrict_mem hD.measurableSet,
      Lp.coeFn_zero ℝ 2 ((volume : Measure R3).restrict D)] with x hxU hxD hx0
    exact (hxU.symm.trans (hUD x hxD)).trans hx0.symm
  have hwE : w = 0 := Subtype.ext hwzero
  exact sub_eq_zero.mp hwE

end OAI.AnisotropicCalderon.Regularity

#print axioms OAI.AnisotropicCalderon.Regularity.classicalHarmonicL2Space
#print axioms OAI.AnisotropicCalderon.Regularity.injective_restrict_classicalHarmonicL2Space
