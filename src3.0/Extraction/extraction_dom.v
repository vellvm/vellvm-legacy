Require Import extraction_core.
Require Import pull_iter.
Require Import push_iter.
Require Import dfs.
Require Import dom_libs.
Require Import Ordered.
Require Import dom_list.
Require Import dom_set.
Require Import dom_tree.
Require Import dom_list_tree.
Require Import dom_set_tree.
Require Import dom_list_df.

Extract Constant OrderedInt.wordsize_one => "O".

Extraction Library dom_libs.
Extraction Library dfs.
Extraction Library pull_iter.
Extraction Library push_iter.
Extraction Library dom_list.
Extraction Library dom_tree.
Extraction Library dom_list_df.
Extraction Library dom_list_tree.
Extraction Library dom_set_tree.
Extraction Library dom_set.
Recursive Extraction Library FSetAVL.
Recursive Extraction Library FSetFacts.
Recursive Extraction Library Ordered.
