.open:

.PHONY: open

DEFAULT_FILE = $(CURDIR)/theory/MyNat.thy

open:
	isabelle jedit -d . $(DEFAULT_FILE)

