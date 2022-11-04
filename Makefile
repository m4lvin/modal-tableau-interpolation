default:
	stack build

test:
	stack test

watchweb:
	stack build --file-watch --exec "bash -c \"pkill tapdleau; stack exec tapdleau &\""

.PHONY: default test watchweb
