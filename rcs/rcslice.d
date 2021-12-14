/+
Outside of a few core. utilities, this is self-contained for now (no Phobos, etc.),
to facilitate testing with betterC.
This would need to be split eventually. Allocation should come from allocators,
initialization should be in its own module, etc. etc.

The implementation is pretty dumbfire, but should offer grounds for a concrete
examination of how exactly it clashes with language invariants.

General impressions are one to one with Andrei Alexandrescu's outline:
https://forum.dlang.org/thread/smc5jb$2u8t$1@digitalmars.com

CONCERNS:

- Purity. Right now this is built on weak purity and outright lies (i.e. GC.add/removeRange).
- Performance. Counters use atomic ops for shared/immutable, and for const require additional
  checking.
- Reaching mutable data through immutable references: Immutable ctors are disabled.
You can still instantiate an empty immutable RCSlice though :*)

ISSUES:

- '@trusted' everywhere, including silly things like 'trustedIf'. Could be reduced somewhat
by putting restrictions on stored types, e.g. requiring their copy ctors/dtors to be @safe.
Which, IMO, should be the way to go. RCSlice can't be any safer than the things it stores.

- Having an RCSlice as a member of a struct with postblit transforms it from a safe facility
into a UB monster, silently. Which may be a problem in generic code. And the best we can do
is say "DO NOT USE IF YOU HAVE POSTBLITS". Or provide an equally bad escape hatch in the form
of a @system public incRef.

- RCSlice!T -> RCSlice!(const(T)) <- RCSlice!(immutable(T))
Implicit conversion from slices of (im)mutable to slices of const looks like could be hacked in via alias this,
however at the present (2.098) implementing such results in DMD segfaulting (LDC doesn't).
Search for EnableImplicitConvToConst to find such instances in unit tests.
The biggest problem is that one of such occurrences is aggregation of an RCSlice into a struct,
making uses of RCSlice severely limited. So at the moment this conversion is disabled for DMD.
Haven't tested with GDC.

- Some code duplication is taking place.

GLOBAL TODO:

- Destructor qualifiers (yuck) need to be checked at instantiation time.
Current implementation may fail for some types if they qualify dtors.

- This needs a metric ton of tests.

- A debug allocator that puts immutables in write-protected pages for good measure.
Consts too when fresh RCSlice!(const(T)) is allocated.

- More `scope` support (from the compiler too. Dennis, rock on!)

- I only tested on Linux. Windows tests and fixes would be appreciated.

+/
module rcs.rcslice;
import core.internal.traits : hasIndirections, hasElaborateDestructor, Unqual, Unconst;

enum bool isMutable(T) = !is(T == const) && !is(T == immutable) && !is(T == inout);

// NOTE: this implementation of `isSafeDestructible` relies on `destroy` from object.d,
// which, arguably, should've been explicitly made @system. But it isn't - it infers for non-classes,
// so I'm using it for the time being just to not reinvent it here.

/// Evaluates to `true` if T is safely destructible
enum bool isSafeDestructible(T) = !hasElaborateDestructor!T || is(typeof((T* ptr) @safe { destroy(*ptr); }));

/// Evaluates to `true` if `To` is copyable from `From`.
/// This explicitly checks copy-initialization and ignores implicit conversions,
/// so e.g. a `ulong` is not considered copyable from `uint` according to this test.
enum bool isCopyable(To, From = To) = is(typeof(inferCopyAttributes!(To, From)));
/// Evaluates to `true` if `To` is safely copyable from `From`.
/// This explicitly checks copy-initialization and ignores implicit conversions,
/// so e.g. a `ulong` is not considered copyable from `uint` according to this test.
enum bool isSafeCopyable(To, From = To) = is(typeof((return scope From* from) @safe => inferCopyAttributes!To(from)));
/// Evaluates to `true` if copying `To` from `From` doesn't throw exceptions.
/// This explicitly checks copy-initialization and ignores implicit conversions,
/// so e.g. a `ulong` is not considered copyable from `uint` according to this test.
enum bool isNothrowCopyable(To, From = To) = is(typeof((return scope From* from) nothrow => inferCopyAttributes!To(from)));

// This is subject to https://issues.dlang.org/show_bug.cgi?id=22499
// A more verbose implementation is possible to work around that, but I'd rather not
// include it here. The bug needs to get fixed!
private void inferCopyAttributes(To, From)(return scope From* from = null)
if (is(immutable To == immutable From))
{
    static if (is(To == struct) && __traits(hasCopyConstructor, To))
    {
        // No extra type, and union trick won't work here anyway,
        // because union with field initialized via copy ctor is not allowed
        // according to the spec.
        To* to;
        to.__ctor(*from);
    }
    else
    {
        union U { To x = To.init; }
        U u = U(*from);
    }
}

// bogus version ID, remove when bug is fixed
version (Issue22499)
unittest
{
    struct Nested
    {
        this (ref return scope inout typeof(this)) {}
    }
    static struct NotNested
    {
        Nested n;
    }
    static assert(isCopyable!NotNested); // should pass, but fails
}

/// Evaluates to `true` if an instance of `T` can be created
/// without supplying initializer.
///
/// This will evaluate to `false` for structs with `@disable`-d
/// default constructor.
enum bool isDefaultInit(T) = is(typeof({ static T x; }));

/// Evaluates to `true` if `T` is a nested struct.
template isNestedStruct(T)
{
    static if (is(T == struct)) enum bool isNestedStruct = __traits(isNested, T);
    else enum bool isNestedStruct = false;
}

// These exist to make compiler yell instead of silently yielding false
// from is(typeof(...)) if the delegate doesn't compile. In the future
// some uses of these should be replaced with is(typeof(...)) variants.
// Around the time ifwhen `scope` gets well.

/// Returns whether a given delegate is `@safe`.
bool isSafe(T)(scope T delegate() @safe) @safe @nogc nothrow pure { return true; }
/// Ditto.
bool isSafe(T)(scope T delegate() @system) @safe @nogc nothrow pure { return false; }

/// Returns whether a given delegate is `nothrow`.
bool isNothrow(T)(scope T delegate() nothrow) @safe @nogc nothrow pure { return true; }
/// Ditto.
bool isNothrow(T)(scope T delegate()) @safe @nogc nothrow pure { return false; }

/// Calls `dg` as `@system` because `test` is `@system`.
///
/// `test` itself is not called.
auto ifSafeThenTrusted(Dg)(scope void delegate() @system test, scope Dg dg) @system
{
    return dg();
}

/// Calls `dg` as `@trusted` because `test` is `@safe`
///
/// `test` itself is not called.
auto ifSafeThenTrusted(Dg)(scope void delegate() @safe test, scope Dg dg) @trusted
{
    return dg();
}

/// Calls `dg` as either `@trusted` or `@system`
/// if `condition` is `true` or `false` respectively
pragma(inline, true)
auto trustedIf(bool condition, Dg)(scope Dg dg)
{
    return { static if (!condition) void* unsafe = void; }
    .ifSafeThenTrusted(dg);
}

version (LDC) enum bool EnableImplicitConvToConst = true;
else
// Enable this to make implicit copying of RCSlice!T -> RCSlice!(const(T)) work,
// and uncover compiler bugs :)
enum bool EnableImplicitConvToConst = false;

struct RCSlice(T)
{
    /// Creates a slice of size `size` with default-initialized elements,
    /// if such initialization is not explicitly disabled.
    ///
    /// Note: this overload is disabled for `T` that is a nested struct,
    /// because it is currently not possible in D to correctly
    /// default-initialize nested structs outside of their parent function.
    this(this This)(size_t size, string file = __FILE__, size_t line = __LINE__) @trusted
    if (isDefaultInit!T && !isNestedStruct!T && isMutable!This)
    {
        if (size)
        {
            repr = allocate(allocationSize(size, file, line));
            auto array = repr.data.all();
            initializeArray(array);
            static if (exposeToGC)
            {
                // cast because could be `shared`
                pureGCAddRange(cast(Unqual!T[]) array, typeid(T));
            }
        }
    }

    /// Creates a slice by copying elements from `init`
    this(U, this This)(scope U[] init, string file = __FILE__, size_t line = __LINE__) scope
    if (isCopyable!(T, U) && isMutable!This)
    {
        if (init.length)
        {
            enum bool safeToDestruct = !is(T == struct) || isSafeDestructible!T;
            // trustedIf... sigh
            trustedIf!(isSafeCopyable!(T, U) && (isNothrowCopyable!(T, U) || safeToDestruct))({
                repr = allocate(allocationSize(init.length, file, line));

                static if (!isNothrowCopyable!(T, U))
                {
                    version (D_Exceptions) scope(failure)
                        deallocate(repr);
                }

                auto array = repr.data.all();
                copyEmplaceArray(init, array);
                static if (exposeToGC)
                {
                    // cast because could be `shared`
                    pureGCAddRange(cast(Unqual!T[]) array, typeid(T));
                }
            });
        }
    }

    /// Creates a slice of size `size` with each element initialized to a copy of `init`
    this(U, this This)(size_t size, U init, string file = __FILE__, size_t line = __LINE__)
    if (isCopyable!(T, U) && isMutable!This)
    {
        if (size)
        {
            enum bool safeToDestruct = !is(T == struct) || isSafeDestructible!T;
            // trustedIf... sigh
            trustedIf!(isSafeCopyable!(T, U) && (isNothrowCopyable!(T, U) || safeToDestruct))({
                repr = allocate(allocationSize(size, file, line));
                static if (!isNothrowCopyable!(T, U))
                {
                    version (D_Exceptions) scope(failure)
                        deallocate(repr);
                }
                auto array = repr.data.all();
                initializeArray(array, init);
                static if (exposeToGC)
                {
                    // cast because could be `shared`
                    pureGCAddRange(cast(Unqual!T[]) array, typeid(T));
                }
            });
        }
    }

    //
    // Copy ctors
    //

    this(ref return scope inout typeof(this) other) return scope @trusted
    {
        repr = cast(Repr) other.repr;
        incRef(repr.block);
    }

    // Because immutable ctor is explicitly disabled, this one needs to be explicitly defined :(
    this(ref return scope inout typeof(this) other) const return scope @trusted
    {
        repr = cast(const(Repr)) other.repr;
        incRef(repr.block);
    }

    @disable this(ref return scope inout typeof(this) other) immutable;

    //
    // Not-really-copy ctors
    //

    this(U, this This)(auto ref return scope inout RCSlice!U other) @trusted
    if (is(U* : T*) && isMutable!This)
    {
        repr = cast(This.Repr) other.repr;
        incRef(repr.block);
    }

    ~this()
    {
        // trustedIf... sigh
        // Unqual here is due to dtor qualifiers. Bleh...
        trustedIf!(!is(T == struct) || isSafeDestructible!(Unqual!T))({
            destructor();
        });
    }

    // Implicit conversion to RCSlice!(const(T))
    static if (EnableImplicitConvToConst && !is(T == const))
    {
        RCSlice!(const(T)) toConst(this This)() @trusted
        {
            alias R = typeof(return);
            R.Repr tmp = cast(R.Repr) repr;
            R.incRef(tmp.block);
            return R(tmp);
        }
        alias toConst this;
    }

    /// Assigns another slice to `this`. If `this` contains last reference to its data,
    /// that data is deallocated before this operator returns.
    @safe
    void opAssign(typeof(this) rhs) scope
    {
        auto tmp = typeof(this)(repr);
        repr = rhs.repr;
        incRef(repr.block);
    }

    /// Assigns to `this` another slice with different element mutability,
    /// if such conversion is allowed by the type system.
    /// If `this` contains last reference to its data,
    /// that data is deallocated before this operator returns.
    void opAssign(U)(auto ref inout RCSlice!U rhs) scope @trusted
    if (is(U* : T*))
    {
        version (none)
        {
            auto tmp = this;
            static if (__traits(isRef, rhs))
            {
                repr = cast(Repr) rhs.repr;
                incRef(repr.block);
            }
            else
            {
                repr = cast(Repr) rhs.repr;
                cast() rhs.repr = rhs.repr.init;
            }
        }
        else
        {
            auto r = cast(Repr) rhs.repr;
            incRef(r.block);
            auto tmp = typeof(this)(r);
            static if (__traits(isRef, rhs))
            {
                repr = cast(Repr) rhs.repr;
                incRef(repr.block);
            }
            else
            {
                repr = cast(Repr) rhs.repr;
                cast() rhs.repr = rhs.repr.init;
            }
        }
    }

    static if (!is(T == const) && !is(T == immutable))
    {
        /// Copy-assigns elements of `array` to elements of `this`.
        /// Array sizes must match.
        void opAssign(A)(return auto ref A array)
        if (is(A : U[], U))
        in
        {
            version (D_NoBoundsChecks)
            {
                assert(array.length == length);
            }
        }
        do
        {
            version (D_NoBoundsChecks) {}
            else
            {
                // TODO: doesn't seem to be a fitting error exposed in core.exception
                if (array.length != length)
                    assert(0, "Array length mismatch");
            }
            repr.data.all()[] = array;
        }
    }

    /// Returns true if corresponding elements of `this` and `rhs` are equal.
    bool opEquals(U, this This)(auto ref scope RCSlice!U rhs) scope
    if (is(typeof(() => U.init == This.init.front())))
    {
        return repr.data.all() == rhs.repr.data.all();
    }

    /// Returns true if corresponding elements of `this` and `rhs` are equal.
    bool opEquals(U, this This)(scope U[] rhs) scope
    if (is(typeof(() => U.init == This.init.front())))
    {
        return repr.data.all() == rhs;
    }

    This opBinary(string op, U, this This)(auto ref return scope RCSlice!U rhs, string file = __FILE__, size_t line = __LINE__)
    if (op == "~")
    {
        const size_t total = length + rhs.length;
        if (!total)
            return This.init;
        enum bool safeToDestruct = !is(T == struct) || isSafeDestructible!T;
        enum bool deducedSafety =
        {
            return isSafeCopyable!T &&
                   isSafeCopyable!(T, U) &&
                   ((isNothrowCopyable!T && isNothrowCopyable!(T, U)) ||
                    safeToDestruct);
        }();
        // trustedIf... sigh
        return trustedIf!deducedSafety({
            auto result = allocate(allocationSize(total, file, line));
            static if (!isNothrowCopyable!T || !isNothrowCopyable!(T, U))
            {
                version (D_Exceptions) scope (failure)
                    deallocate(result);
            }
            copyEmplaceConcat(result.data.all(), repr.data.all(), rhs.repr.data.all());
            static if (exposeToGC)
            {
                // cast because could be `shared`
                pureGCAddRange(cast(Unqual!T[]) result.data.all(), typeid(T));
            }
            return This(result);
        });
    }

    void opOpAssign(string op, U)(auto ref return scope RCSlice!U rhs, string file = __FILE__, size_t line = __LINE__)
    if (op == "~")
    {
        // TODO: use realloc for PODs (only without indirections if exposeToGC)
        this = this.opBinary!op(rhs, file, line);
    }

    /// Returns current number of references.
    size_t refCount() const @trusted
    {
        return fetchRefCount(cast(Block*) repr.block);
    }

    /// Returns length of this slice.
    size_t length() const
    {
        return repr.data.size;
    }

    /// Ditto.
    size_t opDollar() const
    {
        return length;
    }

    static if (!is(Unqual!T == void))
    {
        /// Returns a reference to i-th element of this slice.
        ref opIndex(size_t i, string file = __FILE__, size_t line = __LINE__) inout return
        {
            return bounds(i, file, line);
        }

        static if (!is(T == immutable) && !is(T == const))
        {
            /// Assigns `v` to i-th element of this slice.
            void opIndexAssign(V)(return auto ref V v, size_t i, string file = __FILE__, size_t line = __LINE__)
            {
                import core.lifetime : forward;
                bounds(i, file, line) = forward!v;
            }

            /// Op-assigns `v` to i-th element of this slice.
            void opIndexOpAssign(string op, V)(return auto ref V v, size_t i, string file = __FILE__, size_t line = __LINE__)
            {
                import core.lifetime : forward;
                mixin("bounds(i, file, line) ", op, "= forward!v;");
            }
        }
    }

    /// Returns a slice referencing the same data as `this`.
    RCSlice!T opIndex()
    {
        return opSlice(0, length);
    }

    /// Ditto.
    RCSlice!T opIndex() const
    {
        return opSlice(0, length);
    }

    /// Returns a subslice referencing data of `this`.
    RCSlice!T opSlice(this This)(size_t i, size_t j, string file = __FILE__, size_t line = __LINE__) @trusted
    {
        typeof(return) result = void;
        result.repr = This.Repr(bounds(i, j, file, line), cast(result.Block*) incRef(repr.block));
        return result;
    }

    /// Creates a new slice with copies of elements in this slice,
    /// with their mutability stripped, if such conversion is allowed
    /// by the type system.
    RCSlice!(Unconst!T) dup(this This)() return
    if (isCopyable!(Unconst!T, typeof(This.init.front())))
    {
        return typeof(return)(repr.data.all());
    }

    /// Creates a new slice with immutable copies of elements of this slice,
    /// if such conversion is allowed by the type system.
    RCSlice!(immutable(T)) idup()() const return
    if (isCopyable!(immutable(T), T))
    {
        return typeof(return)(repr.data.all());
    }

    // Not sure this is needed
    /+
    RCSlice!U opCast(X : RCSlice!U, U)() const return @trusted
    if (is(T* : U*))
    {
        typeof(return) result = void;
        result.repr = cast(result.Repr) repr;
        result.incRef(result.repr.block);
        return result;
    }
    +/

    /// Calls `dg`, passing underlying slice to it as argument.
    auto apply(Dg, this This)(scope Dg dg) return scope
    if (is(typeof((return scope T[] a) @safe => dg(a))))
    {
        // Borrow another reference until caller is done with our data,
        // in case `dg` attampts to dangle `this`.
        static if (false && !EnableImplicitConvToConst)
        {
            This tmp = this;
            return dg(tmp.repr.data.all());
        }
        else
        {
            This.Repr tmpRepr = this.repr;
            incRef(tmpRepr.block);
            This tmp = tmpRepr;
            return dg(tmpRepr.data.all());
        }
    }

    void toString(Sink, Spec)(scope Sink sink, scope ref const Spec spec) scope @trusted
    {
        import std.format : formatValue;
        sink("[");
        if (length)
        {
            for (size_t i = 0; i < length - 1; ++i)
            {
                formatValue(sink, repr.data.ptr[i], spec);
                sink(", ");
            }
            formatValue(sink, repr.data.ptr[length-1], spec);
        }
        sink("]");
    }

    /// Returns `true` if this slice references no data.
    bool empty() const
    {
        return length == 0;
    }

    /// Returns a reference to first element of this slice.
    ref front() inout return scope
    {
        return bounds(0, __FILE__, __LINE__);
    }

    /// Returns a reference to last element of this slice.
    ref back() inout return scope
    {
        return bounds(length-1, __FILE__, __LINE__);
    }

    /// Shortens this slice by one from the start.
    void popFront() @trusted
    {
        repr.data = bounds(1, length, __FILE__, __LINE__);
    }

    /// Shortens this slice by one from the end.
    void popBack() @trusted
    {
        repr.data = bounds(0, length-1, __FILE__, __LINE__);
    }

    //
    // opApply madness follows...
    // Could be shortened with std.format, but betterC won't take that kindly.
    //

    enum forwardForeachBody0 = q{
        for (size_t i = 0; i < length; ++i)
        {
            if (auto result = dg(repr.data.one(i)))
                return result;
        }
        return 0;
    };

    enum forwardForeachBody1 = q{
        for (size_t i = 0; i < length; ++i)
        {
            if (auto result = dg(i, repr.data.one(i)))
                return result;
        }
        return 0;
    };

    enum reverseForeachBody0 = q{
        for (size_t i = length - 1; i < length; --i)
        {
            if (auto result = dg(repr.data.one(i)))
                return result;
        }
        return 0;
    };

    enum reverseForeachBody1 = q{
        size_t index;
        for (size_t i = length - 1; i < length; --i, ++index)
        {
            if (auto result = dg(index, repr.data.one(i)))
                return result;
        }
        return 0;
    };

    // With pitchforks, shovels, and lots of swear words...
    // How about we have a couple more attributes, huh?..
    static foreach (constness; [["T", ""], ["const(T)", "const"]])
    {
        static foreach (combo; ["", "@safe", "@nogc", "nothrow", "pure",
                                "@safe @nogc", "@safe nothrow", "@safe pure",
                                "@nogc nothrow", "@nogc pure", "nothrow pure",
                                "@safe @nogc nothrow", "@safe @nogc pure", "@safe nothrow pure",
                                "@nogc nothrow pure",
                                "@safe @nogc nothrow pure"])
        {
            mixin("int opApply(scope int delegate(ref ", constness[0], ") ", combo, " dg) scope ", constness[1] , " {",
                      forwardForeachBody0,
                  "}");

            mixin("int opApply(scope int delegate(size_t, ref ", constness[0], ") ", combo, " dg) scope ", constness[1] , " {",
                      forwardForeachBody1,
                  "}");

            mixin("int opApplyReverse(scope int delegate(ref ", constness[0], ") ", combo, " dg) scope ", constness[1] , " {",
                      reverseForeachBody0,
                  "}");

            mixin("int opApplyReverse(scope int delegate(size_t, ref ", constness[0], ") ", combo, " dg) scope ", constness[1] , " {",
                      reverseForeachBody1,
                  "}");
        }
    }

    invariant()
    {
        // Either we have a valid block and valid data,
        // or we don't have a block and data is null.
        // NOTE: removing `this.` results in lots and lots of unfunny error messages.
        // Compiler bug?

        if (this.repr.block)
        {
            auto counter = counterFor(cast(Block*) this.repr.block);
            assert(counter);
            assert(counter.rc);
            assert(counter.rc != size_t.max);
            assert(this.repr.data.ptr >= this.repr.block.payload.ptr);
            assert(this.repr.data.ptr + this.repr.data.size <= this.repr.block.payload.ptr + this.repr.block.size);
        }
        else
        {
            assert(this.repr is Repr.init);
        }
    }

private:

    this(this This)(Repr r) @trusted
    {
        this.repr = cast(This.Repr) r;
    }

    void destructor() scope @system
    {
        auto block = repr.block;
        if (!decRef(block))
        {
            static if (!is(T == class) && !is(T == interface) && hasElaborateDestructor!T)
            {
                auto payload = block.payload.ptr[0 .. block.size];
                foreach_reverse (ref e; payload)
                {
                    // TODO: there's an issue with dtors vs. const dtors :\
                    destroy(*cast(Unqual!T*) &e);
                }
            }

            deallocate(repr);
        }
    }

    // Our representation
    struct Repr
    {
        // basically a raw slice, because we're re-implementing bounds checking
        // for nicer error messages
        View data;
        // pointer to full original slice
        Block* block;
    }

    struct View
    {
        size_t size;
        T* ptr;

        // This thing is private, all the bounds checks are done
        // a level above. Not particularly fond of this solution,
        // need something better without this silly "trusted" thing
        // that shouldn't actually be trusted at all.
    @trusted:

        // this[i]
        ref one(size_t i) return inout { return ptr[i]; }
        // this[]
        auto all() inout return { return ptr[0 .. size]; }
        // this[i .. j]
        auto sub(size_t i, size_t j) return inout
        {
            return View(j - i, cast(T*) (ptr + i));
        }
    }

    // Full allocated slice
    struct Block
    {
        size_t size;
        T[0] payload;
    }

    // Ties this all together.
    // Only allocate, deallocate, and ref count bumpers ever see this.
    struct Descriptor
    {
        CounterBlock rc;
        Block block;
    }

    Repr repr;

    // BC for single element access
    ref bounds(size_t i, string file, size_t line) inout return
    {
        version (D_NoBoundsChecks)
        {
            assert(i < length);
        }
        else if (i >= length)
        {
            indexError(i, length, file, line);
        }
        return repr.data.one(i);
    }

    // BC for (sub)slice access
    auto bounds(size_t i, size_t j, string file, size_t line) inout return
    {
        version (D_NoBoundsChecks)
        {
            assert(i <= j);
            assert(j <= length);
        }
        else if ((i > j) || (j > length))
        {
            sliceError(i, j, length, file, line);
        }
        return repr.data.sub(i, j);
    }

    enum payloadOffset = Descriptor.block.offsetof + Block.payload.offsetof;

    // Validates requested allocation size,
    // will drop an Error if size overflows
    struct AllocationSize
    {
        size_t numElements;
        size_t numBytes;
    }

    static AllocationSize allocationSize(size_t numElements, string file, size_t line)
    {
        import core.checkedint : addu, mulu;

        bool overflow;
        static if (T.sizeof > 1)
            const payloadSize = mulu(numElements, T.sizeof, overflow);
        else
            alias payloadSize = numElements;

        size_t numBytes = addu(payloadSize, payloadOffset, overflow);

        if (overflow)
        {
            version (D_Exceptions)
            {
                import core.exception : onRangeError;
                onRangeError(file, line);
                static if (!is(typeof(onRangeError()) == noreturn))
                    assert(0);
            }
            else assert(0, "Overflow");
        }

        return AllocationSize(numElements, numBytes);
    }

    // Increases our reference counter (duh)
    static BlockType* incRef(BlockType)(BlockType* block) @trusted
    if (is(immutable BlockType == immutable Block))
    {
        fudgeRefCount(block, 1);
        return block;
    }

    // Decreases our reference counter (duh)
    static size_t decRef(BlockType)(BlockType* block) @trusted
    if (is(immutable BlockType == immutable Block))
    {
        return fudgeRefCount(block, -1);
    }

    static size_t fudgeRefCount(BlockType)(BlockType* block, size_t delta)
    {
        // Slices of unshared const are ignorant of their roots,
        // so they have to do a runtime check to see which kind of op
        // (atomic or not) to do on the counter.
        // For other qualifiers the type of op is statically known:
        // immutable is implicitly shared, so atomic;
        // shared - atomic;
        // mutable unshared - raw

        static if (is(T == shared) || is(T == immutable))
            alias fudge = fudgeShared;
        else static if (!is(T == const))
            alias fudge = .fudge;
        else
            alias fudge = fudgeChecked;

        size_t result = size_t.max;
        return block ? fudge(counterFor(cast(Block*) block), delta) : size_t.max;
    }

    static size_t fetchRefCount(Block* block)
    {
        static if (is(T == shared) || is(T == immutable))
            alias fetch = fetchShared;
        else static if (!is(T == const))
            alias fetch = .fetch;
        else
            alias fetch = fetchChecked;

        return block ? fetch(counterFor(block)) : 0;
    }

    enum exposeToGC = haveDRuntime && hasIndirections!T;

    static Repr allocate(AllocationSize size) @system
    in
    {
        assert((size.numBytes - payloadOffset) == size.numElements * T.sizeof);
    }
    do
    {
        auto ptr = cast(Descriptor*) alignedAlloc(size.numBytes, Descriptor.alignof);
        ptr || outOfMemoryError();
        ptr.rc.rc = 0;
        static if (is(T == shared) || is(T == immutable))
        {
            ptr.rc.flags = 1;
            fudgeShared(&ptr.rc, 1);
        }
        else
        {
            ptr.rc.flags = 0;
            ptr.rc.rc = 1;
        }
        auto block = &ptr.block;
        block.size = size.numElements;
        return Repr(View(block.size, block.payload.ptr), block);
    }

    static void deallocate(ref Repr repr) @system
    in
    {
        assert(repr.block);
        assert(counterFor(repr.block));
        assert(counterFor(repr.block).rc == 0);
    }
    do
    {
        static if (exposeToGC)
        {
            pureGCRemoveRange(cast(void*) repr.block.payload.ptr);
        }
        alignedFree(descriptorFor(repr.block));
        repr = Repr.init;
    }

    // Gets our super private parts
    pragma(inline, true)
    static Descriptor* descriptorFor(Block* p) @trusted
    {
        return cast(Descriptor*) (cast(ubyte*) p - Descriptor.block.offsetof);
    }

    // Also gets our super private parts
    pragma(inline, true)
    static CounterBlock* counterFor(Block* p) @trusted
    {
        return &descriptorFor(p).rc;
    }

    static noreturn indexError(size_t i, size_t length, string file, size_t line)
    {
        version (D_Exceptions)
        {
            import core.exception : onArrayIndexError;
            onArrayIndexError(i, length, file, line);
            static if (!is(typeof(onArrayIndexError(0, 0)) == noreturn))
                assert(0);
        }
        else assert(0, "Array index out of bounds");
    }

    static noreturn sliceError(size_t i, size_t j, size_t length, string file, size_t line)
    {
        version (D_Exceptions)
        {
            import core.exception : onArraySliceError;
            onArraySliceError(i, j, length, file, line);
            static if (!is(typeof(onArraySliceError(0, 0, 0)) == noreturn))
                assert(0);
        }
        else assert(0, "Array slice out of bounds");
    }
}

private noreturn outOfMemoryError() @nogc @safe pure nothrow
{
    version (D_Exceptions)
    {
        import core.exception : onOutOfMemoryError;
        onOutOfMemoryError();
        static if (!is(typeof(onOutOfMemoryError()) == noreturn))
            assert(0);
    }
    else assert(0, "Out of memory");
}

private void initializeArray(T)(T[] array)
{
    static if (__traits(isZeroInit, T))
    {
        auto tptr = cast(ubyte[T.sizeof]*) array.ptr;
        tptr[0 .. array.length] = (ubyte[T.sizeof]).init;
    }
    else
    {
        import core.internal.lifetime : emplaceIntializer;

        auto tptr = cast(Unqual!T*) array.ptr;

        for (size_t i = 0; i < array.length; ++i)
            emplaceInitializer(tptr[i]);
    }
}

private void initializeArray(T, S)(T[] array, ref S init)
if (is(immutable S == immutable T))
{
    static if (__traits(isPOD, T))
    {
        auto sptr = cast(ubyte[T.sizeof]*) &init;
        auto tptr = cast(ubyte[T.sizeof]*) array.ptr;

        for (size_t i = 0; i < array.length; ++i)
            tptr[i] = *sptr;
    }
    else
    {
        import core.lifetime : copyEmplace;

        auto tptr = array.ptr;

        size_t i;
        // This static if seems redundant? Less gunk in debug builds!
        static if (!isNothrow({ copyEmplace(init, array[0]); }))
        {
            version (D_Exceptions) scope (failure)
            {
                static if (hasElaborateDestructor!T)
                    while (i--)
                        destroy(tptr[i]);
            }
        }

        for (; i < array.length; ++i)
            copyEmplace(init, tptr[i]);
    }
}

private void copyEmplaceArray(S, T)(S[] source, T[] target)
if (is(immutable S == immutable T))
in
{
    assert(source.length == target.length);
}
do
{
    static if (__traits(isPOD, T))
    {
        auto sptr = cast(ubyte[S.sizeof]*) source.ptr;
        auto tptr = cast(ubyte[T.sizeof]*) target.ptr;

        for (size_t i = 0; i < target.length; ++i)
            tptr[i] = sptr[i];
    }
    else
    {
        import core.lifetime : copyEmplace;

        auto sptr = source.ptr;
        auto tptr = target.ptr;

        size_t i;
        // This static if seems redundant? Less gunk in debug builds!
        static if (!isNothrow({ copyEmplace(source[0], target[0]); }))
        {
            version (D_Exceptions) scope (failure)
            {
                static if (hasElaborateDestructor!T)
                    while (i--)
                        destroy(tptr[i]);
            }
        }

        for (; i < source.length; ++i)
            copyEmplace(sptr[i], tptr[i]);
    }
}

private void copyEmplaceConcat(T, L, R)(T[] target, L[] left, R[] right)
if (is(immutable T == immutable L) && is(immutable T == immutable R))
in
{
    assert(target.length == left.length + right.length);
}
do
{
    auto tleft = target[0 .. left.length];
    auto tright = target[left.length .. $];
    copyEmplaceArray(left, tleft);
    // This static if seems redundant? Less gunk in debug builds!
    static if (!isNothrow({ copyEmplaceArray(right, tright); }))
    {
        version (D_Exceptions) scope (failure)
        {
            static if (hasElaborateDestructor!T)
                foreach_reverse (ref e; tleft)
                    destroy(e);
        }
    }
    copyEmplaceArray(right, tright);
}

//@betterC
version (none)
@safe @nogc pure nothrow unittest
{
    static assert(__traits(compiles, { RCSlice!int s = 0; }));
    static assert(__traits(compiles, { const RCSlice!int s = 0; }));
    static assert(__traits(compiles, { immutable RCSlice!int s = 0; }));

    static assert(__traits(compiles, { RCSlice!(const(int)) s = 0; }));
    static assert(__traits(compiles, { const RCSlice!(const(int)) s = 0; }));
    static assert(__traits(compiles, { immutable RCSlice!(const(int)) s = 0; }));
    static assert(__traits(compiles, { RCSlice!(immutable(int)) s = 0; }));
    static assert(__traits(compiles, { const RCSlice!(immutable(int)) s = 0; }));
    static assert(__traits(compiles, { immutable RCSlice!(immutable(int)) s = 0; }));
}

//@betterC
version(none)
@safe @nogc pure nothrow unittest
{
    const RCSlice!int c;
    RCSlice!int m = c;
    static assert( isCopyable!(RCSlice!int, const(RCSlice!int)));
    static assert( isCopyable!(RCSlice!int, immutable(RCSlice!int)));
    static assert(!isCopyable!(RCSlice!int, RCSlice!(const(int))));
    static assert(!isCopyable!(RCSlice!int, RCSlice!(immutable(int))));

    static assert( isCopyable!(RCSlice!(const(int)), RCSlice!int));
    static assert( isCopyable!(RCSlice!(const(int)), RCSlice!(const(int))));
    static assert( isCopyable!(RCSlice!(const(int)), RCSlice!(immutable(int))));
    static assert( isCopyable!(RCSlice!(immutable(int)), RCSlice!(immutable(int))));

    static assert( isCopyable!(const(RCSlice!int), RCSlice!int));
    static assert( isCopyable!(const(RCSlice!int), const(RCSlice!int)));
    static assert( isCopyable!(const(RCSlice!int), immutable(RCSlice!int)));

    static assert( isCopyable!(immutable(RCSlice!int), RCSlice!int));
    static assert( isCopyable!(immutable(RCSlice!int), const(RCSlice!int)));
    static assert( isCopyable!(immutable(RCSlice!int), immutable(RCSlice!int)));

    static assert( isCopyable!(const(RCSlice!(const(int))), RCSlice!int));
    static assert( isCopyable!(const(RCSlice!(const(int))), const(RCSlice!int)));
    static assert( isCopyable!(const(RCSlice!(const(int))), const(RCSlice!(const(int)))));

    static assert(!isCopyable!(RCSlice!int, const(RCSlice!(const(int)))));
    static assert(!isCopyable!(RCSlice!int, immutable(RCSlice!(const(int)))));

    static assert(!isCopyable!(RCSlice!(immutable(int)), RCSlice!int));
    static assert(!isCopyable!(RCSlice!(immutable(int)), RCSlice!(const(int))));
    static assert(!isCopyable!(const(RCSlice!(immutable(int))), RCSlice!int));
    static assert(!isCopyable!(immutable(RCSlice!(immutable(int))), RCSlice!(const(int))));

    static assert( isCopyable!(immutable(RCSlice!(immutable(int))), RCSlice!(immutable(int))));
}

//@betterC
@safe @nogc pure nothrow unittest
{
    RCSlice!int sm;
    RCSlice!(const(int)) sc;
    RCSlice!(immutable(int)) si;

    static assert(!__traits(compiles, sm = sc));
    static assert(!__traits(compiles, sm = si));
    static assert( __traits(compiles, sc = sm));
    static assert( __traits(compiles, sc = si));
    static assert(!__traits(compiles, si = sm));
    static assert(!__traits(compiles, si = sc));

    const RCSlice!int csm;
    const RCSlice!(const(int)) csc;
    const RCSlice!(immutable(int)) csi;

    static assert( __traits(compiles, sm = csm));
    static assert(!__traits(compiles, sm = csc));
    static assert(!__traits(compiles, sm = csi));
    static assert( __traits(compiles, sc = csm));
    static assert( __traits(compiles, sc = csc));
    static assert( __traits(compiles, sc = csi));
    static assert(!__traits(compiles, si = csm));
    static assert(!__traits(compiles, si = csc));
    static assert( __traits(compiles, si = csi));

    immutable RCSlice!int ism;
    immutable RCSlice!(const(int)) isc;
    immutable RCSlice!(immutable(int)) isi;

    static assert( __traits(compiles, sm = ism));
    static assert(!__traits(compiles, sm = isc));
    static assert(!__traits(compiles, sm = isi));
    static assert( __traits(compiles, sc = ism));
    static assert( __traits(compiles, sc = isc));
    static assert( __traits(compiles, sc = isi));
    static assert(!__traits(compiles, si = ism));
    static assert(!__traits(compiles, si = isc));
    static assert( __traits(compiles, si = csi));
}

//@betterC
@safe @nogc pure nothrow unittest
{
    void takeMutable(RCSlice!int) {}
    void takeConst(const RCSlice!int) {}

    RCSlice!int sm;
    const RCSlice!int sc;
    immutable RCSlice!int si;

    static assert( is(typeof(() { takeMutable(sm); })));
    static assert( is(typeof(() { takeMutable(sc); })));
    static assert( is(typeof(() { takeMutable(si); })));

    static assert(is(typeof(() { takeConst(sm); })));
    static assert(is(typeof(() { takeConst(sc); })));
    static assert(is(typeof(() { takeConst(si); })));
}

//@betterC
@safe @nogc pure nothrow unittest
{
    void takeMutable(RCSlice!(const(int))) {}
    void takeConst(const RCSlice!(const(int))) {}

    static if (EnableImplicitConvToConst)
    {{
        RCSlice!int sm;
        const RCSlice!int sc;
        immutable RCSlice!int si;

        static assert( is(typeof(() { takeMutable(sm); })));
        static assert( is(typeof(() { takeMutable(sc); })));
        static assert( is(typeof(() { takeMutable(si); })));

        static assert( is(typeof(() { takeConst(sm); })));
        static assert( is(typeof(() { takeConst(sc); })));
        static assert( is(typeof(() { takeConst(si); })));
    }}

    {
        RCSlice!(const(int)) sm;
        const RCSlice!(const(int)) sc;
        immutable RCSlice!(const(int)) si;

        static assert(is(typeof(() { takeMutable(sm); })));
        static assert(is(typeof(() { takeMutable(sc); })));
        static assert(is(typeof(() { takeMutable(si); })));

        static assert(is(typeof(() { takeConst(sm); })));
        static assert(is(typeof(() { takeConst(sc); })));
        static assert(is(typeof(() { takeConst(si); })));
    }
}

//@betterC
@safe @nogc pure nothrow unittest
{
    void takeMutable(RCSlice!(immutable(int))) {}
    void takeConst(const RCSlice!(immutable(int))) {}

    {
        RCSlice!int sm;
        const RCSlice!int sc;
        immutable RCSlice!int si;

        static assert(!is(typeof(() { takeMutable(sm); })));
        static assert(!is(typeof(() { takeMutable(sc); })));
        static assert(!is(typeof(() { takeMutable(si); })));

        static assert(!is(typeof(() { takeConst(sm); })));
        static assert(!is(typeof(() { takeConst(sc); })));
        static assert(!is(typeof(() { takeConst(si); })));
    }

    {
        RCSlice!(const(int)) sm;
        const RCSlice!(const(int)) sc;
        immutable RCSlice!(const(int)) si;

        static assert(!is(typeof(() { takeMutable(sm); })));
        static assert(!is(typeof(() { takeMutable(sc); })));
        static assert(!is(typeof(() { takeMutable(si); })));

        static assert(!is(typeof(() { takeConst(sm); })));
        static assert(!is(typeof(() { takeConst(sc); })));
        static assert(!is(typeof(() { takeConst(si); })));
    }

    {
        RCSlice!(immutable(int)) sm;
        const RCSlice!(immutable(int)) sc;
        immutable RCSlice!(immutable(int)) si;

        static assert(is(typeof(() { takeMutable(sm); })));
        static assert(is(typeof(() { takeMutable(sc); })));
        //static assert(is(typeof(() { takeMutable(si); }))); // TODO: should!

        static assert(is(typeof(() { takeConst(sm); })));
        static assert(is(typeof(() { takeConst(sc); })));
        //static assert(is(typeof(() { takeConst(si); }))); // TODO: should!
    }
}

//@betterC
@safe @nogc pure nothrow unittest
{
    RCSlice!int s = 4;
    assert(s == s);
    assert(s == [0, 0, 0, 0]);
}

//@betterC
@safe @nogc pure nothrow unittest
{
    int[1] before = [42];
    RCSlice!int s = 1;
    int[1] after = [34];
    s = before;
    assert(s == [42]);
    s = after;
    assert(s == [34]);
}

//@betterC
@safe @nogc pure nothrow unittest
{
    RCSlice!(int*) s;
    int local;
    static assert(!isSafe({ s[0] = &local; }));
    int*[1] array = [&local];
    static assert(!isSafe({ s = array; }));
    static assert(!isSafe({ s[0] = array[0]; }));
}

//@betterC
@safe @nogc nothrow unittest
{
    static RCSlice!(int*) glob;
    int local;
    int*[1] array = [&local];
    RCSlice!(int*) s = array;

    // TODO: this currently fails. The ctor above should take
    // the array as return scope, but doing that brings the @nogc error
    // right back. Compiler should be smarter about scope arrays.
    //static assert(!isSafe({ glob = s; }));
}

//@betterC
@safe @nogc pure nothrow unittest
{
    RCSlice!int s = [1, 2, 3];
    assert(s.refCount == 1);
    auto c = s;
    assert(s.refCount == 2);
    c = c.dup;
    assert(s.refCount == 1);
    assert(c.refCount == 1);
    assert(c == s);
    assert(c !is s);
}

//@betterC
@safe @nogc pure nothrow unittest
{
    RCSlice!int s = 1;
    (copy) {
        assert(copy.refCount == 2);
    } (s);
    assert(s.refCount == 1);
    (ref reference) {
        assert(reference.refCount == 1);
    } (s);
}

// Segfault could be related to https://issues.dlang.org/show_bug.cgi?id=22593
static if (EnableImplicitConvToConst)
@safe @nogc pure nothrow unittest
{
    static struct PB
    {
        RCSlice!int slice;

        this(this)
        {
            // Because this is a postblit, no copy ctor is called,
            // therefore RCSlice is silently broken when it is a member
            // of structs that have postblits. Transitively :\
            // With not so much as a squeak from the compiler :\

            // ...RCSlice could provide a @system public method to increase
            // refcount, although it'd be better if this nonsense
            // dichotomy ended before this century is done.
            //assert(slice.refCount == 2);
        }
    }

    RCSlice!int s = 1;
    {
        PB pb = PB(s);
        assert(s.refCount == 2);
        auto copy = pb;

        // This is only here to make this unittest not do anything nasty,
        // real user code won't be able to do this
        () @trusted { s.incRef(s.repr.block); } ();
    }
    // accessing s after this point would be UB in real code,
    // since it would be dangling
}

//@betterC
@safe @nogc pure nothrow unittest
{
    RCSlice!(const(int)*) s;
    () {
        int*[] a;
        s = a;
        return s;
    } ();
}

//@betterC
@safe @nogc pure nothrow unittest
{
    RCSlice!(immutable(int)) si;
    static assert(is(immutable(int)* : const(int)*));
    RCSlice!(const(int)) sc = si;
    static assert(!is(typeof(() { RCSlice!int sm = si; })));
    static assert(!is(typeof(() { RCSlice!int sm = sc; })));
}

version(unittest)
// a simplistic version of std.algorithm.mutation.copy
auto copy(T, R)(scope T[] src, R range)
{
    while (!range.empty && src.length)
    {
        range.front = src[0];
        range.popFront;
        src = src[1 .. $];
    }
    return range;
}

//@betterC
@safe @nogc pure nothrow unittest
{
    int[4] data = [1, 2, 3, 4];
    RCSlice!int s = 10;
    auto rem = data.copy(s);
    assert(s[0 .. data.length] == data);
    assert(s != data);
    assert(rem == s[data.length .. $]);
}

//@betterC
@safe @nogc nothrow unittest
{
    static int[] glob;

    void escape(int[] a) { glob = a; }
    void compilerWillSeeNoEscape(int[]) @safe {}

    static assert(!__traits(compiles, {
        RCSlice!int s;
        s.apply(&escape);
    }));

    static assert( isSafe({
        RCSlice!int s;
        s.apply(&compilerWillSeeNoEscape);
    }));
}

version (unittest)
long sum()(const RCSlice!(const(int)) input)
{
    long result;
    foreach (i; input)
        result += i;
    return result;
}

//@betterC
@safe @nogc pure nothrow unittest
{
    RCSlice!int s = [1, 2, 3, 4];
    RCSlice!(const(int)) sc = s;

    static if (EnableImplicitConvToConst)
        assert(sum(s) == 10);
    assert(sum(sc) == 10);
    assert(sum(RCSlice!(const(int))([1, 2, 3, 4])) == 10);
}

//@betterC
@safe @nogc pure nothrow unittest
{
    static struct S
    {
        int* cctors;
        int* dtors;
        this(ref return scope typeof(this) other)
        {
            this.tupleof = other.tupleof;
            ++*cctors;
        }
        ~this() { ++*dtors; }
    }

    {
        RCSlice!S sm;
        RCSlice!(immutable(S)) si;
        static assert(!is(typeof(() => sm.idup)));
        static assert(!is(typeof(() => si.idup)));
    }

    {
        int cctors;
        int dtors;
        {
            auto s = RCSlice!S(32, S(&cctors, &dtors));
            auto c = s;
        }
        assert(cctors == 32);
        assert(dtors == 33);
    }

    {
        int cctors;
        int dtors;
        {
            auto s = RCSlice!S(32, S(&cctors, &dtors));
            auto c = s.dup;
        }
        assert(cctors == 64);
        assert(dtors == 65);
    }
}

@safe @nogc pure nothrow unittest
{
    static auto create(scope int[] arr)
    {
        RCSlice!int result = arr;
        return result;
    }

    auto s1 = create([1, 2, 3, 4]);
    auto s2 = s1 ~ create([5, 6, 7, 8]);
    assert(s2 == [1, 2, 3, 4, 5, 6, 7, 8]);
    s1 ~= create([5, 6, 7, 8]);
    assert(s1 == s2);

    assert(s1 !is s2);
    assert(s1.refCount == 1);
    assert(s2.refCount == 1);
}

@safe @nogc nothrow unittest
{
    static RCSlice!(int*) ss;
    // Funny thing, removing this `return` will make compiler
    // silently allow the escape, and the static assert at the end
    // will trigger
    static auto create(return scope int*[] arr)
    {
        RCSlice!(int*) result = arr;
        return result;
    }

    int a, b, c;
    int*[3] pointers = [&a, &b, &c];
    auto s1 = create(pointers);
    auto s2 = s1 ~ create(pointers);
    s1 ~= create(pointers);
    assert(s1 == s2);

    assert(s1 !is s2);
    assert(s1.refCount == 1);
    assert(s2.refCount == 1);

    static assert(!isSafe({ ss = s1; }));
}

private:

struct CounterBlock
{
    size_t rc;
    // TODO: currently just a single bit is used to indicate
    // that data started out as immutable. Could pack it into
    // the counter itself...
    ubyte flags;
}

pragma(inline, true)
@system @nogc nothrow pure
size_t fudge(CounterBlock* block, size_t delta)
in
{
    assert (!block.flags);
}
do
{
    block.rc += delta;
    return block.rc;
}

pragma(inline, true)
@system @nogc nothrow pure
size_t fudgeShared(CounterBlock* block, size_t delta)
in
{
    assert (block.flags == 1);
}
do
{
    import core.atomic : atomicOp;
    return (cast(shared) block).rc.atomicOp!"+="(delta);
}

pragma(inline, true)
@system @nogc nothrow pure
size_t fudgeChecked(CounterBlock* counter, size_t n)
{
    return (counter.flags & 1) ? fudgeShared(counter, n) : fudge(counter, n);
}

pragma(inline, true)
@system @nogc nothrow pure
size_t fetch(CounterBlock* block)
in
{
    assert (!block.flags);
}
do
{
    return block.rc;
}

pragma(inline, true)
@system @nogc nothrow pure
size_t fetchShared(CounterBlock* block)
in
{
    assert (block.flags == 1);
}
do
{
    import core.atomic : atomicLoad;
    return (cast(shared) block).rc.atomicLoad;
}

pragma(inline, true)
@system @nogc nothrow pure
size_t fetchChecked(CounterBlock* counter)
{
    return (counter.flags & 1) ? fetchShared(counter) : fetch(counter);
}

version (FreeStanding)   enum haveDRuntime = false;
else version (D_BetterC) enum haveDRuntime = false;
else                     enum haveDRuntime = true;

// TODO: make alignedAlloc/alignedFree always have D linkage
extern(C)
{
    static if (haveDRuntime)
    {
        // Let's lie a (not so little) bit.

        @system @nogc nothrow pure
        pragma(mangle, "fakePureGCAddRange")
        void pureGCAddRange(const(void)[] block, const TypeInfo ti);

        @system @nogc nothrow pure
        pragma(mangle, "fakePureGCRemoveRange")
        void pureGCRemoveRange(const(void)* ptr);

        pragma(inline, true)
        void fakePureGCAddRange(const(void)[] block, const TypeInfo ti)
        {
            import core.memory : GC;
            GC.addRange(cast(void*) block.ptr, block.length, ti);
        }

        pragma(inline, true)
        void fakePureGCRemoveRange(const(void)* ptr)
        {
            import core.memory : GC;
            return GC.removeRange(cast(void*) ptr);
        }
    }

    //
    // alignedAlloc, alignedFree
    //

    version (FreeStanding)
    {
        // I.e. freestanding callers would have to implement these two
        @system @nogc nothrow pure
        void* _druntime_aligned_alloc(size_t size, size_t alignment);
        @system @nogc nothrow pure
        void _druntime_free(void* ptr);

        alias alignedAlloc = _druntime_aligned_alloc;
        alias alignedFree = _druntime_free;
    }
    else version (Windows)
    {
        version (CRuntime_DigitalMars)
        {
            // NOTE: implementation copied from std.experimental.allocator.mallocator
            struct AlignInfo
            {
                void* basePtr;
                size_t size;

                @nogc nothrow
                static AlignInfo* opCall(void* ptr)
                {
                    return cast(AlignInfo*) (ptr - AlignInfo.sizeof);
                }
            }

            @nogc nothrow
            void* _aligned_malloc(size_t size, size_t alignment)
            {
                import core.stdc.stdlib : malloc;
                size_t offset = alignment + size_t.sizeof * 2 - 1;

                // unaligned chunk
                void* basePtr = malloc(size + offset);
                if (!basePtr) return null;

                // get aligned location within the chunk
                void* alignedPtr = cast(void**)((cast(size_t)(basePtr) + offset)
                    & ~(alignment - 1));

                // write the header before the aligned pointer
                AlignInfo* head = AlignInfo(alignedPtr);
                head.basePtr = basePtr;
                head.size = size;

                return alignedPtr;
            }

            @system @nogc nothrow pure
            pragma(mangle, "fakePure_aligned_free")
            void _aligned_free(void*);

            void fakePure_aligned_free(void *ptr)
            {
                import core.memory : pureFree;
                if (!ptr) return;
                AlignInfo* head = AlignInfo(ptr);
                pureFree(head.basePtr);
            }
        }
        else
        {
            @system @nogc nothrow void* _aligned_malloc(size_t size, size_t alignment);
            @system @nogc nothrow pure void _aligned_free(void*);
        }

        alias alignedFree = _aligned_free;

        @system @nogc nothrow pure
        pragma(mangle, "fakePureAlignedAlloc")
        void* alignedAlloc(size_t size, size_t alignment);

        void* fakePureAlignedAlloc(size_t size, size_t alignment)
        {
            import core.stdc.errno;
            auto save = errno;
            scope (exit) errno = save;
            return _aligned_malloc(size, alignment);
        }
    }
    else version (Posix)
    {
        @system @nogc nothrow pure
        int posix_memalign(void** memptr, size_t alignment, size_t size);

        @system @nogc nothrow pure
        void* alignedAlloc(size_t size, size_t alignment)
        {
            void* ptr;
            if (auto result = posix_memalign(&ptr, alignment < (void*).sizeof ? (void*).sizeof : alignment, size))
                return null;
            return ptr;
        }
        import core.memory : alignedFree = pureFree;
    }
}
