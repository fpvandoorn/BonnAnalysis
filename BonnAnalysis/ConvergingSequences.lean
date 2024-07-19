import Mathlib.Topology.Sequences
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Order
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic.FunProp
-- import Mathlib.Order
-- noncomputable section

--open FourierTransform MeasureTheory Real


namespace MeasureTheory

universe u v
open Order Set Filter
open Filter
open scoped Topology

set_option checkBinderAnnotations false
class SubSequence {X : Type u} (a : ℕ → X) where
   φ : ℕ → ℕ
   hφ : StrictMono φ
--open SubSequence
--@[coe] def coeSubS {X : Type u} {a : ℕ → X}  (σ : SubSequence a): ℕ → X  := a ∘ σ.φ    -- how to not automatically coerce everywhere?
instance {X : Type u} {a : ℕ → X}  :  CoeFun (SubSequence a) (fun _ => ℕ → X) where
  coe σ := a ∘ σ.φ    -- how to not automatically coerce everywhere?
--instance {X Y : Type u} {f : X → Y} {a : ℕ → X} : Coe (SubSequence a) (SubSequence (f ∘ a)) where
--  coe σ := ⟨ σ.φ , σ.hφ⟩
lemma bndOnStrictMono {φ : ℕ → ℕ} (hφ : StrictMono φ) {a : ℕ} : ¬ (φ a < a) := by
      intro ass
      induction' a with n hn
      · exact Nat.not_succ_le_zero (φ 0) ass
      · apply hn
        have : φ (n + 1) ≤ n  := Nat.le_of_lt_succ ass
        apply LE.le.trans_lt' this
        apply hφ
        exact lt_add_one n
lemma subsequencePreservesTop  {φ : ℕ → ℕ}
  (hφ : StrictMono φ) : map φ atTop  ≤ atTop := by
  rw [le_def]
  intro U hU
  simp at hU
  obtain ⟨ a , ha⟩ := hU
  have : ∃ a' , φ a' ≥ a := by
    by_contra ass
    push_neg at ass
    specialize ass a
    apply bndOnStrictMono hφ ass
  simp only [mem_map, mem_atTop_sets, ge_iff_le, mem_preimage]

  use this.choose
  intro b hb
  apply ha
  trans
  exact this.choose_spec
  apply StrictMono.monotone hφ hb

lemma subSeqConverges' {X : Type u} {ι : Type v} {q : Filter ι}{p : Filter X} {a : ι → X}
  {φ : ι → ι}
  (hφ : map φ q ≤ q) (pf : Tendsto a q p)  :
  Tendsto (a ∘ φ) q p := by
    intro U hU
    rw [tendsto_def] at pf
    specialize pf U hU
    rw [mem_map]
    exact hφ pf
lemma subSeqConverges {X : Type u} {p : Filter X} {a : ℕ → X}
  (pf : Tendsto a atTop p) (a' : SubSequence a) :
  Tendsto a' atTop p := subSeqConverges' (subsequencePreservesTop a'.hφ) pf

class ConvergingSequences (X : Type u) where
  seq : (ℕ → X) × X → Prop
  seq_cnst : ∀ x : X , seq (fun _ => x , x )
  seq_sub : ∀ {a x} , seq ( a, x) → ∀ a' : SubSequence a , seq (a' , x)


variable {X : Type u} [ConvergingSequences X]
--notation (priority := high) P "[" A "]" => obj_over (P:=P.1.hom) A
open ConvergingSequences
scoped notation a " ⟶ " x => seq (a , x)
@[simp] def nbh (x : X) : Filter X := by
  use {Y | ∀ a , (a ⟶ x) → Y ∈ map a atTop}
  · simp
  · simp only [mem_map, mem_atTop_sets, ge_iff_le, mem_preimage, mem_setOf_eq] ;
    intro Y Z
    intro ass hYZ b (hb : b ⟶ x)
    specialize ass b hb
    obtain ⟨ a , ha⟩ := ass
    use a
    intro i hi
    apply hYZ
    exact ha i hi
  · intro Y Z hY hZ
    intro a ha
    rw [inter_mem_iff]
    constructor
    apply hY a ha
    apply hZ a ha
    -- def IsSeqClosed (s : Set X) : Prop := ∀ ⦃x : ℕ → X⦄ ⦃p : X⦄, (∀ n, x n ∈ s) ∧ seq (x , p) → p ∈ s

instance fromSeq : TopologicalSpace X := .mkOfNhds nbh

lemma tendsToNbh  {x : X} (a : ℕ → X) (ha : a ⟶ x) : Tendsto a atTop (nbh x) := by
  intro N hN
  apply hN
  exact ha
lemma nbhdCofinalIn𝓝 {x : X} {U} (hU : U ∈ 𝓝 x) : ∃ V ∈ nbh x , V ⊆ U := by
  rw [@mem_nhds_iff] at hU
  obtain ⟨ V , hV ⟩ := hU
  use V
  constructor
  · apply hV.2.1
    exact hV.2.2
  · exact hV.1
lemma tendsTo𝓝  {x : X} (a : ℕ → X) (ha : a ⟶ x) : Tendsto a atTop (𝓝 x) := by
intro U hU
obtain ⟨ V , hV ⟩ := nbhdCofinalIn𝓝 hU
apply mem_of_superset ; swap
· exact hV.2
· apply hV.1
  exact ha

lemma subSeqCnstrction {a : ℕ → X} {Y : Set (X)} (as : Y ∉ map a atTop) :
  ∃ (a' : SubSequence a) , ∀ n , a' n ∉ Y := by
    simp at as
    let φ : ℕ → ℕ := by
      intro n
      induction n with
        | zero => exact (as 0).choose
        | succ _ φn =>  exact ((as (Nat.succ φn)).choose)
    use ⟨ φ , by
      intro n b
      induction b with
        | zero => simp
        | succ b hb =>
          intro as'
          have : φ n ≤ φ b := by
            by_cases h : n = b
            · rw [h] ;
            · exact le_of_lt (hb <| Nat.lt_of_le_of_ne (Nat.le_of_lt_succ as') h)
          exact Nat.lt_of_le_of_lt this (as (Nat.succ (φ b))).choose_spec.1
       ⟩
    intro n
    simp
    induction n with
      | zero => exact (as 0).choose_spec.2
      | succ n _ => exact ((as (Nat.succ (φ n))).choose_spec.2)

lemma seqInNhd {a : ℕ → X} {N : Set X} (hN : N ∈ map a atTop) : ∃ n , a n ∈ N := by
    simp at hN
    use hN.choose
    apply hN.choose_spec
    exact le_rfl

lemma important (x : X) (N : Set X) (p : N ∈ 𝓝 x) : N ∈ nbh x := by
  rw [mem_nhds_iff] at p



  obtain ⟨ U , ⟨ q , r , p⟩ ⟩ := p
  exact mem_of_superset (r x p) q
@[fun_prop] structure SeqContinuous' {Y : Type v} [TopologicalSpace Y] (f : X → Y) : Prop where
  seqCont :∀ {x} {a : X} , (x ⟶ a) → Tendsto (f ∘ x) atTop (𝓝 (f a))
open SeqContinuous'

@[fun_prop] lemma continuous_of_SeqContinuous {Y : Type v} [TopologicalSpace Y] {f : X → Y}
  (hf : SeqContinuous' f) : Continuous f := by
    apply continuous_iff_isClosed.mpr
    intro C hC
    rw [← @isOpen_compl_iff]
    intro x hx a ha
    by_contra φ
    obtain ⟨ a' , ha' ⟩ := subSeqCnstrction φ
    simp at ha'
    apply hx
    have hC : IsSeqClosed C := IsClosed.isSeqClosed hC

    apply hC
    · exact ha'
    · intro N hN
      sorry
      --apply seqCont

      --
      --apply seq_sub ha
      --exact hN
  --#align continuous_of_SeqContinuous continuous.seq_continuous'

/-
instance SeqSpaceFromConv: SequentialSpace X where
  isClosed_of_seq := by
    intro A p
    rw [← @isOpen_compl_iff]
    intro x hx a ha
    by_contra φ
    obtain ⟨ a' , ha' ⟩ := subSeqCnstrction φ
    simp at ha'
    apply hx
    apply p
    · exact ha'
    · intro N hN
      apply important x N hN a'
      apply seq_sub
      exact ha
-/
