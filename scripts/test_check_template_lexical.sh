#!/usr/bin/env bash
# Self-test of scripts/check_template_lexical.sh: every way of writing a forbidden token that the gate must see,
# and every harmless spelling it must not trip on. Each "bad" case was either a bypass of the old line-anchored
# grep (marked OLD-BYPASS) or a form it caught and must keep catching.
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
gate="$here/check_template_lexical.sh"
dir=$(mktemp -d); trap 'rm -rf "$dir"' EXIT
fail=0

# case <expect: bad|clean> <name> <lean source, printf-style>
case_() {
  local expect=$1 name=$2; printf '%b' "$3" > "$dir/$name.lean"
  if bash "$gate" "$dir/$name.lean" >/dev/null 2>&1; then got=clean; else got=bad; fi
  if [ "$got" != "$expect" ]; then echo "FAIL $name: expected $expect, gate said $got"; fail=1; fi
}

imp='import ForShor.ShorVerification.Framework.FullRunDesign\n'

# ---- must be refused
case_ bad plain_implemented_by   "${imp}@[implemented_by evil] def sub : Nat := 1\n"
case_ bad attribute_cmd          "${imp}attribute [implemented_by evil] sub\n"
case_ bad attribute_local        "${imp}attribute [local implemented_by evil] sub\n"
case_ bad extern                 "${imp}@[extern \"x\"] opaque sub : Nat\n"
case_ bad csimp                  "${imp}@[csimp] theorem x : 1 = 1 := rfl\n"
case_ bad export_then_impl       "${imp}@[export foo, implemented_by evil] def sub : Nat := 1\n"
case_ bad stacked_attrs          "${imp}@[inline] @[implemented_by evil] def sub : Nat := 1\n"          # OLD-BYPASS
case_ bad after_open_in          "${imp}open Lean in @[implemented_by evil] def sub : Nat := 1\n"       # OLD-BYPASS
case_ bad after_doc_comment      "${imp}/-- doc -/ @[implemented_by evil] def sub : Nat := 1\n"         # OLD-BYPASS
case_ bad multiline_attr         "${imp}@[simp,\n implemented_by evil] def sub : Nat := 1\n"            # OLD-BYPASS
case_ bad after_namespace        "${imp}namespace Foo @[implemented_by evil] def sub : Nat := 1\n"      # OLD-BYPASS
case_ bad run_cmd_after_open     "${imp}open Lean Elab Command in run_cmd logInfo \"x\"\n"              # OLD-BYPASS
case_ bad unsafe_after_set_opt   "${imp}set_option maxRecDepth 100 in unsafe def sub : Nat := 1\n"      # OLD-BYPASS
case_ bad guillemets             "${imp}@[«implemented_by» evil] def sub : Nat := 1\n"
case_ bad after_string_dashes    "${imp}def s := \"--\" @[implemented_by evil] def sub : Nat := 1\n"
case_ bad after_closed_nested    "${imp}/- a /- b -/ -/ @[implemented_by evil] def sub : Nat := 1\n"
case_ bad after_block_comment    "${imp}/- c -/ @[extern \"x\"] opaque sub : Nat\n"
case_ bad after_raw_string       "${imp}def s := r#\"--\"# @[implemented_by evil] def sub : Nat := 1\n"
case_ bad after_char_quote       "${imp}def c := '\"' @[implemented_by evil] def sub : Nat := 1\n"
case_ bad init_attr              "${imp}@[init foo] def sub : Nat := 1\n"
case_ bad builtin_init_attr      "${imp}@[builtin_init] def sub : Nat := 1\n"
case_ bad multiline_init_attr    "${imp}@[simp,\n init foo] def sub : Nat := 1\n"
case_ bad word_in_string         "${imp}def s := \"implemented_by\"\n"       # strings are scanned as code on purpose
for kw in unsafe run_cmd run_meta run_elab initialize builtin_initialize elab elab_rules macro macro_rules \
          syntax declare_syntax_cat notation; do
  case_ bad "kw_$kw" "${imp}$kw foo\n"
done
case_ bad import_lean            "import Lean\n"
case_ bad import_lean_sub        "import Lean.Elab.Command\n"
case_ bad set_option_debug       "${imp}set_option debug.skipKernelTC true\n"
case_ bad unterminated_comment   "${imp}/- never closed\n@[simp] def x := 1\n"
case_ bad unterminated_string    "${imp}def s := \"never closed\n"

# ---- must pass
case_ clean prose_line_comment   "${imp}-- uses implemented_by, unsafe and run_cmd in prose only\ndef x : Nat := 1\n"
case_ clean prose_doc_comment    "${imp}/-- \`@[implemented_by f]\` and \`unsafe\` are refused. -/\ndef x : Nat := 1\n"
case_ clean prose_nested_block   "${imp}/- a /- @[implemented_by f] -/ run_cmd -/\ndef x : Nat := 1\n"
case_ clean module_doc           "${imp}/-! # Notes: extern, csimp, macro, syntax -/\ndef x : Nat := 1\n"
case_ clean ordinary_attrs       "${imp}@[simp, inline, reducible] def x : Nat := 1\n@[simp] theorem t : 1 = 1 := rfl\n"
case_ clean similar_identifiers  "${imp}def externalCount := 1\ndef unsafeCast' := 2\ndef my_macro := 3\ndef initY1 := 4\ndef syntaxTree := 5\n"
case_ clean list_init            "${imp}def l := List.init 3 id\n"
case_ clean primes_and_chars     "${imp}def x' := 'a'\ndef y := '\\\\n'\ndef z := '\"'\n"
case_ clean import_other         "import Mathlib.Data.Nat.Basic\n"
case_ clean empty                ""

# ---- usage
bash "$gate" "$dir/does_not_exist.lean" >/dev/null 2>&1; [ $? -eq 2 ] || { echo "FAIL missing file: expected exit 2"; fail=1; }

if [ $fail -eq 0 ]; then echo "test_check_template_lexical: all cases behave"; fi
exit $fail
