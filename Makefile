HS_TARGETS = $(patsubst %.hs,%,$(wildcard *.hs))
HS_OBJS = $(patsubst %.hs,%.o,$(wildcard *.hs))
HS_INTERFACES = $(patsubst %.hs,%.hi,$(wildcard *.hs))

C_TARGETS = $(patsubst %.c,%,$(wildcard *.c))
C_OBJS = $(patsubst %.c,%.o,$(wildcard *.c))

all: $(HS_TARGETS) $(C_TARGETS)

clean:
	rm -f $(HS_TARGETS) $(HS_OBJS) $(HS_INTERFACES)
	rm -f $(C_TARGETS) $(C_OBJS)

$(HS_TARGETS): %: %.hs
	ghc -Wall -fwarn-tabs -fwarn-incomplete-record-updates -fwarn-monomorphism-restriction -fwarn-unused-do-bind $<

$(C_TARGETS): %: %.c
	gcc -g3 -Wall -Wextra -o $@ $<
