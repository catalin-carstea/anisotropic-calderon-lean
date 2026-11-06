import Calderon.CollaboratorRegularityBaseCaseOct17
import Calderon.CollaboratorFixedSobolevCalculusOct17
import Calderon.CollaboratorRegularityAlgebraHOct17
import Calderon.CollaboratorRegularityDiffEquationOct17
import Calderon.CollaboratorRotationH10Oct17

/-! Task 05, higher orders: `H^m(B)` as a submodule of `L²(B)` and the inductive step. -/

noncomputable section
open MeasureTheory TopologicalSpace Metric
open scoped InnerProductSpace ContDiff Distributions Gradient Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.Regularity.HO
open TauCeti TauCeti.PDE EnergyBridge

/-- `L²(B)`. -/
@[inline, reducible] def L2B := Lp ℝ 2 ((volume : Measure R3).restrict ballOpens)

/-- The values of `H^m(B)` functions, as a submodule of `L²(B)`. -/
def Hs (m : ℕ) : Submodule ℝ L2B :=
  LinearMap.range
    (Wkp.valueL (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) m).toLinearMap

theorem mem_Hs {m : ℕ} {g : L2B} :
    g ∈ Hs m ↔ ∃ G : Wkp (volume : Measure R3) ballOpens 2 m, Wkp.value m G = g := by
  simp only [Hs, LinearMap.mem_range, ContinuousLinearMap.coe_coe, Wkp.valueL_apply]

theorem Hs_succ_le (m : ℕ) : Hs (m + 1) ≤ Hs m := fun g hg => by
  obtain ⟨G, hG⟩ := mem_Hs.mp hg
  exact mem_Hs.mpr ⟨Wkp.lowerOrder m G, by rw [← Wkp.value_succ]; exact hG⟩

theorem Hs_le {m n : ℕ} (h : m ≤ n) : Hs n ≤ Hs m := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact (Hs_succ_le _).trans ih

theorem mem_Hs_zero (g : L2B) : g ∈ Hs 0 := mem_Hs.mpr ⟨g, rfl⟩

/-! ### Membership up to a.e. equality -/

theorem aeIn_congr {P : Submodule ℝ L2B} {f g : R3 → ℝ} (hf : AEIn P f)
    (hfg : f =ᵐ[(volume : Measure R3).restrict ballOpens] g) : AEIn P g := by
  obtain ⟨h, hP, hh⟩ := hf
  exact ⟨h, hP, hh.trans hfg⟩

theorem aeIn_of_mem {P : Submodule ℝ L2B} {g : L2B} (hg : g ∈ P) : AEIn P g := ⟨g, hg, by rfl⟩

theorem mem_of_aeIn {P : Submodule ℝ L2B} {g : L2B} (hg : AEIn P g) : g ∈ P := by
  obtain ⟨h, hP, hh⟩ := hg
  rwa [← Lp.ext hh]

theorem aeIn_add {P : Submodule ℝ L2B} {f g : R3 → ℝ} (hf : AEIn P f) (hg : AEIn P g) :
    AEIn P (fun x => f x + g x) := by
  obtain ⟨h₁, hP₁, hh₁⟩ := hf
  obtain ⟨h₂, hP₂, hh₂⟩ := hg
  refine ⟨h₁ + h₂, P.add_mem hP₁ hP₂, ?_⟩
  filter_upwards [Lp.coeFn_add h₁ h₂, hh₁, hh₂] with x h1 h2 h3
  rw [h1, Pi.add_apply, h2, h3]

theorem aeIn_smul {P : Submodule ℝ L2B} {f : R3 → ℝ} (c : ℝ) (hf : AEIn P f) :
    AEIn P (fun x => c * f x) := by
  obtain ⟨h, hP, hh⟩ := hf
  refine ⟨c • h, P.smul_mem c hP, ?_⟩
  filter_upwards [Lp.coeFn_smul c h, hh] with x h1 h2
  rw [h1, Pi.smul_apply, h2, smul_eq_mul]

theorem aeIn_neg {P : Submodule ℝ L2B} {f : R3 → ℝ} (hf : AEIn P f) :
    AEIn P (fun x => -f x) := by
  simpa using aeIn_smul (-1) hf

theorem aeIn_sub {P : Submodule ℝ L2B} {f g : R3 → ℝ} (hf : AEIn P f) (hg : AEIn P g) :
    AEIn P (fun x => f x - g x) := by
  simpa [sub_eq_add_neg] using aeIn_add hf (aeIn_neg hg)

theorem aeIn_sum {P : Submodule ℝ L2B} {ι : Type*} (s : Finset ι) {f : ι → R3 → ℝ}
    (hf : ∀ i ∈ s, AEIn P (f i)) : AEIn P (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨0, P.zero_mem, ?_⟩
      filter_upwards [Lp.coeFn_zero ℝ 2 ((volume : Measure R3).restrict ballOpens)] with x hx
      exact hx
  | insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact aeIn_add (hf a (Finset.mem_insert_self a s))
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))


/-! ### Multipliers, derivatives, and reconstruction -/

theorem exists_iteratedFDeriv_bound {ψ : R3 → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (k : ℕ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ j : ℕ, j ≤ k → ∀ x, ‖iteratedFDeriv ℝ j ψ x‖ ≤ M := by
  have h : ∀ j : ℕ, ∃ C, ∀ x, ‖iteratedFDeriv ℝ j ψ x‖ ≤ C := fun j =>
    ((hψ.continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm.bddAbove_range_of_hasCompactSupport
      (hc.iteratedFDeriv j).norm).imp fun C hC x => hC ⟨x, rfl⟩
  choose C hC using h
  refine ⟨∑ j ∈ Finset.range (k + 1), |C j|, Finset.sum_nonneg fun j _ => abs_nonneg _,
    fun j hj x => (hC j x).trans ((le_abs_self _).trans ?_)⟩
  exact Finset.single_le_sum (f := fun j => |C j|) (fun j _ => abs_nonneg _)
    (Finset.mem_range.mpr (by omega))

theorem aeIn_mul (m : ℕ) {ψ : R3 → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    {g : L2B} (hg : g ∈ Hs m) : AEIn (Hs m) (fun x => ψ x * g x) := by
  obtain ⟨G, rfl⟩ := mem_Hs.mp hg
  obtain ⟨M, hM, hb⟩ := exists_iteratedFDeriv_bound hψ hc (m + 1)
  have key := DirichletFamily.mulAt (Ω := ballOpens) m
  obtain ⟨T, hT, -⟩ := key.choose_spec.2 ψ hψ hc M hM hb
  exact ⟨Wkp.value m (T G), mem_Hs.mpr ⟨_, rfl⟩, hT G⟩

theorem aeIn_partial (m : ℕ) (G : Wkp (volume : Measure R3) ballOpens 2 (m + 1)) (i : Fin 3) :
    AEIn (Hs m) (fun x => W1p.gradient (Wkp.firstOrder m G) x i) :=
  ⟨Wkp.value m (WkpCalculus.d i m G), mem_Hs.mpr ⟨_, rfl⟩, WkpCalculus.value_d i m G⟩

theorem value_mem_Hs_of_partials (m : ℕ) (w : W1p (volume : Measure R3) ballOpens 2)
    (h : ∀ i, AEIn (Hs m) (fun x => W1p.gradient w x i)) : W1p.value w ∈ Hs (m + 1) := by
  choose g hg hge using h
  choose G hG using fun i => mem_Hs.mp (hg i)
  refine mem_Hs.mpr ⟨WkpCalculus.ofPartials m w G fun i => ?_, WkpCalculus.value_ofPartials _ _ _ _⟩
  rw [hG i]
  exact hge i

theorem exists_of_value_mem_Hs (m : ℕ) (w : W1p (volume : Measure R3) ballOpens 2)
    (h : W1p.value w ∈ Hs (m + 1)) :
    ∃ W : Wkp (volume : Measure R3) ballOpens 2 (m + 1), Wkp.firstOrder m W = w := by
  obtain ⟨G, hG⟩ := mem_Hs.mp h
  exact ⟨G, W1p.ext_value (by rw [Wkp.value_firstOrder, hG])⟩

theorem value_firstOrder_mem_Hs (m : ℕ) (W : Wkp (volume : Measure R3) ballOpens 2 (m + 1)) :
    W1p.value (Wkp.firstOrder m W) ∈ Hs (m + 1) :=
  mem_Hs.mpr ⟨W, (Wkp.value_firstOrder m W).symm⟩

end OAI.AnisotropicCalderon.Regularity.HO
