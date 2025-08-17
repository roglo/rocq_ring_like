all:
	cd src; $(MAKE) $(MFLAGS) all

install:
	cd src; $(MAKE) $(MFLAGS) install

uninstall:
	cd src; $(MAKE) $(MFLAGS) install

local_opam_pin_add:
	cd src; $(MAKE) $(MFLAGS) local_opam_pin_add
