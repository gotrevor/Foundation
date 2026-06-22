# OUTGOING-COMMENT — charter instruction defect (web tools in the box)

The autonomous-run charter asserts as fact:

> **You CAN read the open web**: your `WebFetch`/`WebSearch` tools run server-side ...
> For THOSE — or anything WebFetch genuinely can't retrieve — use the online-request hatch.

In this box the web tools are network-clamped: every call 60s-timeouts (no egress).
Two failure modes the wording induces:

1. Presents "web works server-side" as a STANDING FACT; it is environment-dependent. A
   session burns calls trying the literature before discovering there's no network.
2. The fallback trigger "WebFetch genuinely can't retrieve it" is ambiguous between
   "network down" and "wrong page", so the reflex is to RETRY other URLs/hosts/APIs
   (raw.githubusercontent, api.github.com, ...) rather than fall back to ON-LINE-REQUEST.md.

Proposed patch:
- Make it conditional + self-terminating: "Box is normally network-clamped; WebFetch/WebSearch
  usually time out (~60s). Probe with at most ONE call. A 60s timeout == no-network == clamped:
  do NOT retry other URLs/hosts/APIs this lap; go straight to ON-LINE-REQUEST.md and keep
  working locally. Only a 404/redirect/garbage-content (a PAGE problem) justifies a second URL."
- Also: point sessions at LOCAL read-only Foundation clones for upstream-status checks instead
  of the network (see below) — that need never required the web at all.

(Per operator: local read-only Foundation clones exist in several places; use those to compare
against upstream FFL rather than fetching github.)
