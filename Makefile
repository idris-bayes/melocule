all: melocule examples

.PHONY:

builddir = build/

clean:
	rm -rf "$(builddir)*"

melocule:
	pack install-deps melocule.ipkg

twofive: melocule
	pack exec Examples/TwoFive.idr "$(builddir)251.mid"
	midi2ly -o "$(builddir)251.ly" "$(builddir)251.mid"
	lilypond -i format.ly -o "$(builddir)251.png" "$(builddir)251.ly"

blues: melocule
	pack exec Examples/Blues.idr "$(builddir)blues.mid"
	midi2ly -o "$(builddir)blues.ly" "$(builddir)blues.mid"
	lilypond -i format.ly -o "$(builddir)blues.png" "$(builddir)blues.ly"

fmttm: melocule
	pack exec Examples/FlyMeToTheMoon.idr "$(builddir)fmttm.mid"
	midi2ly -o "$(builddir)fmttm.ly" "$(builddir)fmttm.mid"
	lilypond -i format.ly -o "$(builddir)fmttm.png" "$(builddir)fmttm.ly"

examples: twofive blues fmttm
