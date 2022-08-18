all: melocule examples

.PHONY:

builddir = build/
outdir = out/

lyfmt = pdf

clean:
	rm -rf "$(builddir)*"
	rm -rf "$(outdir)*"

melocule:
	pack install-deps melocule.ipkg

twofive: melocule
	pack exec Examples/TwoFive.idr "$(outdir)251.mid"
	midi2ly -o "$(outdir)251.ly" "$(outdir)251.mid"
	lilypond -i format.ly -f $(lyfmt) -o "$(outdir)251" "$(outdir)251.ly"

blues: melocule
	pack exec Examples/Blues.idr "$(outdir)blues.mid"
	midi2ly -o "$(outdir)blues.ly" "$(outdir)blues.mid"
	lilypond -i format.ly -f $(lyfmt) -o "$(outdir)blues" "$(outdir)blues.ly"

fmttm: melocule
	pack exec Examples/FlyMeToTheMoon.idr "$(outdir)fmttm.mid"
	midi2ly -o "$(outdir)fmttm.ly" "$(outdir)fmttm.mid"
	lilypond -i format.ly -f $(lyfmt) -o "$(outdir)fmttm" "$(outdir)fmttm.ly"

examples: twofive blues fmttm
