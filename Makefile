all: melocule midi pdfs

.PHONY:

output-fmt = pdf

builddir = build
outdir = out

run := LD_LIBRARY_PATH=$(shell gsl-config --prefix)/lib pack exec
lycmd := lilypond -f $(output-fmt) #-i format.ly 

clean:
	rm -rf "$(builddir)/*"
	rm -rf "$(outdir)/*"

dependencies:
	pack install-deps melocule.ipkg

melocule: dependencies


twofive: melocule
	$(run) Examples/TwoFive.idr "$(outdir)/251.mid"

blues: melocule
	$(run) Examples/Blues.idr "$(outdir)/blues.mid"

fmttm: melocule
	$(run) Examples/FlyMeToTheMoon.idr "$(outdir)/fmttm.mid"

midi: twofive blues fmttm

pdfs: midi
	for f in $(wildcard $(outdir)/*.mid); do \
		midi2ly -o "$$f.ly" "$$f"; \
		$(lycmd) -o "$$f" "$$f.ly"; \
		rm "$$f.ly"; \
		rm "$$f.midi"; \
	done
