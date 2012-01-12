/*!
 * opal v0.3.15
 * http://opalrb.org
 *
 * Copyright 2012, Adam Beynon
 * Released under the MIT license
 */

(function(undefined) {
var opal = this.opal = {};

// Minify common function calls
var hasOwnProperty  = Object.prototype.hasOwnProperty,
    $slice          = Array.prototype.slice;

// Types - also added to bridged objects
var T_CLASS      = 0x0001,
    T_MODULE     = 0x0002,
    T_OBJECT     = 0x0004,
    T_BOOLEAN    = 0x0008,
    T_STRING     = 0x0010,
    T_ARRAY      = 0x0020,
    T_NUMBER     = 0x0040,
    T_PROC       = 0x0080,
    T_HASH       = 0x0100,
    T_RANGE      = 0x0200,
    T_ICLASS     = 0x0400,
    FL_SINGLETON = 0x0800;

// Generates unique id for every ruby object
var unique_id = 0;

function define_attr(klass, name, getter, setter) {
  if (getter) {
    define_method(klass, mid_to_jsid(name), function() {
      var res = this[name];

      return res == null ? nil : res;
    });
  }

  if (setter) {
    define_method(klass, mid_to_jsid(name + '='), function(block, val) {
      return this[name] = val;
    });
  }
}

/**
 * Hash constructor
 */
function Hash() {
  var args    = $slice.call(arguments),
      assocs  = {},
      key;

  this.map  = assocs;
  this.none = nil;
  this.proc = nil;

  for (var i = 0, length = args.length; i < length; i++) {
    key = args[i];
    assocs[key.$hash()] = [key, args[++i]];
  }

  return this;
};

// Returns new hash with values passed from ruby
opal.hash = Hash;

// Find function body for the super call
function find_super(klass, callee, mid) {
  var cur_method;

  while (klass) {
    if (klass.$m[mid]) {
      if (klass.$m[mid] == callee) {
        cur_method = klass.$m[mid];
        break;
      }
    }
    klass = klass.$s;
  }

  if (!(klass && cur_method)) { return null; }

  klass = klass.$s;

  while (klass) {
    if (klass.$m[mid]) {
      return klass.$m[mid];
    }

    klass = klass.$s;
  }
}

// Jump return - return in proc body
opal.jump = function(value, func) {
  throw new Error('jump return');
};

// Get constant with given id
opal.const_get = function(const_table, id) {
  if (const_table[id]) {
    return const_table[id];
  }

  raise(RubyNameError, 'uninitialized constant ' + id);
};

// Table holds all class variables
opal.cvars = {};

// Array of all procs to be called at_exit
var end_procs = [];

// Call exit blocks in reverse order
opal.do_at_exit = function() {
  var proc;

  while (proc = end_procs.pop()) {
    proc.call(proc.$S);
  }
};

// Globals table
opal.gvars = {};

// Define a method alias
opal.alias = function(klass, new_name, old_name) {
  new_name = mid_to_jsid(new_name);
  old_name = mid_to_jsid(old_name);

  var body = klass.$allocator.prototype[old_name];

  if (!body) {
    raise(RubyNameError, "undefined method `" + old_name + "' for class `" + klass.$name + "'");
  }

  define_method(klass, new_name, body);
  return nil;
};

// method missing yielder - used in debug mode to call method_missing.
opal.mm = function(jsid) {
  var mid = jsid_to_mid(jsid);
  return function() {
    var args = $slice.call(arguments, 1);
    args.unshift(mid);
    return this.$method_missing.apply(this, args);
  };
}

// Actually define methods
var define_method = opal.defn = function(klass, id, body) {
  // If an object, make sure to use its class
  if (klass.$flags & T_OBJECT) {
    klass = klass.$klass;
  }

  // super uses this
  if (!body.$rbName) {
    body.$rbName = id;
  }

  klass.$allocator.prototype[id] = body;

  var included_in = klass.$included_in, includee;

  if (included_in) {
    for (var i = 0, ii = included_in.length; i < ii; i++) {
      includee = included_in[i];

      define_method(includee, id, body);
    }
  }

  if (klass.$bridge_prototype) {
    klass.$bridge_prototype[id] = body;
  }


  return nil;
}

// Fake yielder used when no block given
opal.no_proc = function() {
  raise(RubyLocalJumpError, "no block given");
};

// Create a new Range instance
opal.range = function(beg, end, exc) {
  var range         = new RubyRange.$allocator();
      range.begin   = beg;
      range.end     = end;
      range.exclude = exc;

  return range;
};


function define_module(base, id) {
  var module;

  module             = boot_module();
  module.$name = (base === RubyObject ? id : base.$name + '::' + id)

  make_metaclass(module, RubyModule);

  module.$flags           = T_MODULE;
  module.$included_in = [];

  var const_alloc   = function() {};
  var const_scope   = const_alloc.prototype = new base.$const.alloc();
  module.$const     = const_scope;
  const_scope.alloc = const_alloc;

  base.$const[id]    = module;

  return module;
}

function include_module(klass, module) {
  if (!klass.$included_modules) {
    klass.$included_modules = [];
  }

  if (klass.$included_modules.indexOf(module) != -1) {
    return;
  }

  klass.$included_modules.push(module);

  if (!module.$included_in) {
    module.$included_in = [];
  }

  module.$included_in.push(klass);

  var module_proto = module.$allocator.prototype;
  for (var method in module_proto) {
    if (hasOwnProperty.call(module_proto, method)) {
      if (!klass.$allocator.prototype[method]) {
        define_method(klass, method, module_proto[method]);
      }
    }
  }
}

// opal define class. 0: regular, 1: module, 2: shift class.
opal.klass = function(base, superklass, id, body, type) {
  var klass;

  switch (type) {
    case 0:
      if (base.$flags & T_OBJECT) {
        base = class_real(base.$klass);
      }

      if (superklass === nil) {
        superklass = RubyObject;
      }

      if (hasOwnProperty.call(base.$const, id)) {
        klass = base.$const[id];
      }
      else {
        klass = define_class(base, id, superklass);
      }

      break;

    case 1:
      if (base.$flags & T_OBJECT) {
        base = class_real(base.$klass);
      }

      if (hasOwnProperty.call(base.$const, id)) {
        klass = base.$const[id];
      }
      else {
        klass = define_module(base, id);
      }

      break;

    case 2:
      klass = singleton_class(base);
      break;
  }

  return body.call(klass);
};

opal.slice = $slice;

opal.defs = function(base, id, body) {
  return define_method(singleton_class(base), id, body);
};

// Undefine one or more methods
opal.undef = function(klass) {
  var args = $slice.call(arguments, 1);

  for (var i = 0, length = args.length; i < length; i++) {
    var mid = args[i], id = mid_to_jsid[mid];

    delete klass.$m_tbl[id];
  }
};

// Calls a super method.
opal.zuper = function(callee, self, args) {
  var mid  = callee.$rbName,
      func = find_super(self.$klass, callee, mid);

  if (!func) {
    raise(RubyNoMethodError, "super: no superclass method `" + mid + "'"
             + " for " + self.$inspect());
  }

  return func.apply(self, args);
};

function mid_to_jsid(mid) {
  if (method_names[mid]) {
    return method_names[mid];
  }

  return '$' + mid.replace('!', '$b').replace('?', '$p').replace('=', '$e');
}

function jsid_to_mid(jsid) {
  if (reverse_method_names[jsid]) {
    return reverse_method_names[jsid];
  }

  jsid = jsid.substr(1); // remove '$'

  return jsid.replace('$b', '!').replace('$p', '?').replace('$e', '=');
}

// Raise a new exception using exception class and message
function raise(exc, str) {
  throw exc.$new(str);
}

opal.arg_error = function(given, expected) {
  raise(RubyArgError, 'wrong number of arguments(' + given + ' for ' + expected + ')');
};

// Inspect object or class
function inspect_object(obj) {
  if (obj.$flags & T_OBJECT) {
    return "#<" + class_real(obj.$klass).$name + ":0x" + (obj.$id * 400487).toString(16) + ">";
  }
  else {
    return obj.$name;
  }
}

// Root of all objects and classes inside opal
function RootObject() {};

RootObject.prototype.toString = function() {
  if (this.$flags & T_OBJECT) {
    return "#<" + (this.$klass).$name + ":0x" + this.$id + ">";
  }
  else {
    return '<' + this.$name + ' ' + this.$id + '>';
  }
};

// Boot a base class (makes instances).
function boot_defclass(superklass) {
  var cls = function() {
    this.$id = unique_id++;

    return this;
  };

  if (superklass) {
    var ctor           = function() {};
        ctor.prototype = superklass.prototype;

    cls.prototype = new ctor();
  }
  else {
    cls.prototype = new RootObject();
  }

  cls.prototype.constructor = cls;
  cls.prototype.$flags          = T_OBJECT;

  return cls;
}

// Boot actual (meta classes) of core objects.
function boot_makemeta(id, klass, superklass) {
  var meta = function() {
    this.$id = unique_id++;

    return this;
  };

  var ctor           = function() {};
      ctor.prototype = superklass.prototype;

  meta.prototype = new ctor();

  var proto              = meta.prototype;
      proto.$included_in = [];
      proto.$allocator   = klass;
      proto.$flags       = T_CLASS;
      proto.$name  = id;
      proto.$s           = superklass;
      proto.constructor  = meta;

  var result = new meta();
  klass.prototype.$klass = result;
  result.$proto = klass.prototype;

  return result;
}

// Create generic class with given superclass.
function boot_class(superklass) {
  // instances
  var cls = function() {
    this.$id = unique_id++;

    return this;
  };

  var ctor = function() {};
      ctor.prototype = superklass.$allocator.prototype;

  cls.prototype = new ctor();

  var proto             = cls.prototype;
      proto.constructor = cls;
      proto.$flags          = T_OBJECT;

  // class itself
  var meta = function() {
    this.$id = unique_id++;

    return this;
  };

  var mtor = function() {};
      mtor.prototype = superklass.constructor.prototype;

  meta.prototype = new mtor();

  proto                            = meta.prototype;
  proto.$allocator                 = cls;
  proto.$flags                     = T_CLASS;
  proto.constructor                = meta;
  proto.$s                         = superklass;

  var result = new meta();
  cls.prototype.$klass = result;
  
  result.$proto = cls.prototype;

  return result;
}

function boot_module() {
  // where module "instance" methods go. will never be instantiated so it
  // can be a regular object
  var module_cons = function(){};
  var module_inst = module_cons.prototype;
  
  // Module itself
  var meta = function() {
    this.$id = unique_id++;
    return this;
  };
  
  var mtor = function(){};
  mtor.prototype = RubyModule.constructor.prototype;
  meta.prototype = new mtor();
  
  var proto = meta.prototype;
  proto.$allocator  = module_cons;
  proto.$flags      = T_MODULE;
  proto.constructor = meta;
  proto.$s          = RubyModule;
  
  var module          = new meta();
  module.$proto       = module_inst;
  
  return module;
}

// Get actual class ignoring singleton classes and iclasses.
function class_real(klass) {
  while (klass.$flags & FL_SINGLETON) {
    klass = klass.$s;
  }

  return klass;
}

// Make metaclass for the given class
function make_metaclass(klass, superklass) {
  if (klass.$flags & T_CLASS) {
    if ((klass.$flags & T_CLASS) && (klass.$flags & FL_SINGLETON)) {
      raise(RubyException, "too much meta: return klass?");
    }
    else {
      var class_id = "#<Class:" + klass.$name + ">",
          meta     = boot_class(superklass);

      meta.$name = class_id;
      meta.$allocator.prototype = klass.constructor.prototype;
      meta.$flags |= FL_SINGLETON;

      klass.$klass = meta;

      meta.$const = klass.$const;
      meta.__attached__ = klass;

      return meta;
    }
  }
  else {
    return make_singleton_class(klass);
  }
}

function make_singleton_class(obj) {
  var orig_class = obj.$klass,
      class_id   = "#<Class:#<" + orig_class.$name + ":" + orig_class.$id + ">>";

  klass             = boot_class(orig_class);
  klass.$name = class_id;

  klass.$flags                |= FL_SINGLETON;
  klass.$bridge_prototype  = obj;

  obj.$klass = klass;

  klass.__attached__ = obj;

  klass.$klass = class_real(orig_class).$k;

  return klass;
}

function bridge_class(constructor, flags, id) {
  var klass     = define_class(RubyObject, id, RubyObject),
      prototype = constructor.prototype;

  klass.$allocator = constructor;
  klass.$proto = prototype;

  bridged_classes.push(klass);

  prototype.$klass = klass;
  prototype.$flags = flags;

  return klass;
}

// Define new ruby class
function define_class(base, id, superklass) {
  var klass;

  var class_id = (base === RubyObject ? id : base.$name + '::' + id);

  klass             = boot_class(superklass);
  klass.$name = class_id;

  make_metaclass(klass, superklass.$klass);

  var const_alloc   = function() {};
  var const_scope   = const_alloc.prototype = new base.$const.alloc();
  klass.$const      = const_scope;
  const_scope.alloc = const_alloc;

  base.$const[id] = klass;

  if (superklass.$inherited) {
    superklass.$inherited(null, klass);
  }

  return klass;
}

// Get singleton class of obj
function singleton_class(obj) {
  var klass;

  if (obj.$flags & T_OBJECT) {
    if ((obj.$flags & T_NUMBER) || (obj.$flags & T_STRING)) {
      raise(RubyTypeError, "can't define singleton");
    }
  }

  if ((obj.$klass.$flags & FL_SINGLETON) && obj.$klass.__attached__ == obj) {
    klass = obj.$klass;
  }
  else {
    var class_id = obj.$klass.$name;

    klass = make_metaclass(obj, obj.$klass);
  }

  return klass;
}

opal.main = function(id) {
  opal.gvars.$0 = find_lib(id);

  try {
    top_self.$require(id);

    opal.do_at_exit();
  }
  catch (e) {
    // this is defined in debug.js
    console.log(e.$klass.$name + ': ' + e.message);
    console.log("\t" + e.$backtrace().join("\n\t"));
  }
};

/**
 * Register a standard file. This can be used to register non-lib files.
 * For example, specs can be registered here so they are available.
 *
 * NOTE: Files should be registered as a full path with given factory.
 *
 * Usage:
 *
 *    opal.file('/spec/foo.rb': function() {
 *      // ...
 *    });
 */
opal.file = function(file, factory) {
  FACTORIES[file] = factory;
};

/**
 * Register a lib.
 *
 * Usage:
 *
 *    opal.lib('my_lib', function() {
 *      // ...
 *    });
 *
 *    opal.lib('my_lib/foo', function() {
 *      // ...
 *    });
 */
opal.lib = function(lib, factory) {
  var file        = '/lib/' + lib + '.rb';
  FACTORIES[file] = factory;
  LIBS[lib]       = file;
};

var FACTORIES    = {},
    LIBS         = {},
    LOADER_PATHS = ['', '/lib'],
    LOADER_CACHE = {};

function find_lib(id) {
  var path;

  // try to load a lib path first - i.e. something in our load path
  if (path = LIBS[id]) return path;

  // find '/opal/x' style libs
  if (path = LIBS['opal/' + id]) return path;

  // next, incase our require() has a ruby extension..
  if (FACTORIES['/lib/' +id]) return '/lib/' + id;

  // check if id is full path..
  if (FACTORIES[id]) return id;

  // full path without '.rb'
  if (FACTORIES[id + '.rb']) return id + '.rb';

  // check in current working directory.
  var in_cwd = FS_CWD + '/' + id;

  if (FACTORIES[in_cwd]) return in_cwd;
};

// Current working directory
var FS_CWD = '/';

// Turns a glob string into a regexp
function fs_glob_to_regexp(glob) {
  var parts  = glob.split(''),
      length = parts.length,
      result = '';

  var opt_group_stack = 0;

  for (var i = 0; i < length; i++) {
    var cur = parts[i];

    switch (cur) {
      case '*':
        if (parts[i + 1] === '*' && parts[i + 2] === '/') {
          result += '.*';
          i += 2;
        }
        else {
          result += '[^/]*';
        }
        break;

      case '.':
        result += '\\';
        result += cur;
        break;

      case ',':
        if (opt_group_stack) {
          result += '|';
        }
        else {
          result += ',';
        }
        break;

      case '{':
        result += '(';
        opt_group_stack++;
        break;

      case '}':
        if (opt_group_stack) {
          result += ')';
          opt_group_stack--;
        }
        else {
          result += '}'
        }
        break;

      default:
        result += cur;
    }
  }

  return new RegExp('^' + result + '$');
};

// Initialization
// --------------

// The *instances* of core objects
var BootObject = boot_defclass();
var BootModule = boot_defclass(BootObject);
var BootClass  = boot_defclass(BootModule);

// The *classes' of core objects
var RubyObject = boot_makemeta('Object', BootObject, BootClass);
var RubyModule = boot_makemeta('Module', BootModule, RubyObject.constructor);
var RubyClass = boot_makemeta('Class', BootClass, RubyModule.constructor);

// Fix boot classes to use meta class
RubyObject.$klass = RubyClass;
RubyModule.$klass = RubyClass;
RubyClass.$klass = RubyClass;

// fix superclasses
RubyObject.$s = null;
RubyModule.$s = RubyObject;
RubyClass.$s = RubyModule;

opal.Object = RubyObject;
opal.Module = RubyModule;
opal.Class  = RubyClass;

// make object act like a module
var bridged_classes = RubyObject.$included_in = [];

// Top level Object scope (used by object and top_self).
var top_const_alloc     = function(){};
var top_const_scope     = top_const_alloc.prototype;
top_const_scope.alloc   = top_const_alloc; 

RubyObject.$const = opal.constants = top_const_scope;

var module_const_alloc = function(){};
var module_const_scope = new top_const_alloc();
module_const_scope.alloc = module_const_alloc;
RubyModule.$const = module_const_scope;

var class_const_alloc = function(){};
var class_const_scope = new top_const_alloc();
class_const_scope.alloc = class_const_alloc;
RubyClass.$const = class_const_scope;

RubyObject.$const.BasicObject = RubyObject;
RubyObject.$const.Object = RubyObject;
RubyObject.$const.Module = RubyModule;
RubyObject.$const.Class = RubyClass;

RubyModule.$allocator.prototype.$donate = function(methods) {
  var included_in = this.$included_in, includee, method, table = this.$proto, dest;

  if (included_in) {
    for (var i = 0, length = included_in.length; i < length; i++) {
      includee = included_in[i];
      dest = includee.$proto;
      for (var j = 0, jj = methods.length; j < jj; j++) {
        method = methods[j];
        // if (!dest[method]) {
          dest[method] = table[method];
        // }
      }
      // if our includee is itself included in another module/class then it
      // should also donate its new methods
      if (includee.$included_in) {
        includee.$donate(methods);
      }
    }
  }
};

var top_self = opal.top = new RubyObject.$allocator();

var RubyNilClass  = define_class(RubyObject, 'NilClass', RubyObject);
var nil = opal.nil = new RubyNilClass.$allocator();

bridge_class(Array, T_OBJECT | T_ARRAY, 'Array');
bridge_class(Number, T_OBJECT | T_NUMBER, 'Numeric');

bridge_class(Hash, T_OBJECT, 'Hash');

bridge_class(String, T_OBJECT | T_STRING, 'String');
bridge_class(Boolean, T_OBJECT | T_BOOLEAN, 'Boolean');
bridge_class(Function, T_OBJECT | T_PROC, 'Proc');
bridge_class(RegExp, T_OBJECT, 'Regexp');

var RubyMatch     = define_class(RubyObject, 'MatchData', RubyObject);
var RubyRange     = define_class(RubyObject, 'Range', RubyObject);

var RubyException      = bridge_class(Error, T_OBJECT, 'Exception');
var RubyStandardError  = define_class(RubyObject, 'StandardError', RubyException);
var RubyRuntimeError   = define_class(RubyObject, 'RuntimeError', RubyException);
var RubyLocalJumpError = define_class(RubyObject, 'LocalJumpError', RubyStandardError);
var RubyTypeError      = define_class(RubyObject, 'TypeError', RubyStandardError);
var RubyNameError      = define_class(RubyObject, 'NameError', RubyStandardError);
var RubyNoMethodError  = define_class(RubyObject, 'NoMethodError', RubyNameError);
var RubyArgError       = define_class(RubyObject, 'ArgumentError', RubyStandardError);
var RubyScriptError    = define_class(RubyObject, 'ScriptError', RubyException);
var RubyLoadError      = define_class(RubyObject, 'LoadError', RubyScriptError);
var RubyIndexError     = define_class(RubyObject, 'IndexError', RubyStandardError);
var RubyKeyError       = define_class(RubyObject, 'KeyError', RubyIndexError);
var RubyRangeError     = define_class(RubyObject, 'RangeError', RubyStandardError);
var RubyNotImplError   = define_class(RubyObject, 'NotImplementedError', RubyException);

RubyException.$allocator.prototype.toString = function() {
  return this.$klass.$name + ': ' + this.message;
};

var breaker = opal.breaker  = new Error('unexpected break');
    breaker.$klass              = RubyLocalJumpError;
    breaker.$t              = function() { throw this; };



      var method_names = {'==': '$eq$', '===': '$eqq$', '[]': '$aref$', '[]=': '$aset$', '~': '$tild$', '<=>': '$cmp$', '=~': '$match$', '+': '$plus$', '-': '$minus$', '/': '$div$', '*': '$mul$', '<': '$lt$', '<=': '$le$', '>': '$gt$', '>=': '$ge$', '<<': '$lshft$', '>>': '$rshft$', '|': '$or$', '&': '$and$', '^': '$xor$', '+@': '$uplus$', '-@': '$uminus$', '%': '$mod$', '**': '$pow$'};
      var reverse_method_names = {};
      for (var id in method_names) {
        reverse_method_names[method_names[id]] = id;
      }
    
(function($opal) {var nil = $opal.nil, $const = $opal.constants, _a, $breaker = $opal.breaker, $no_proc = $opal.no_proc, $klass = $opal.klass, $const_get = $opal.const_get, $slice = $opal.slice;
($opal.gvars["$LOAD_PATH"] = ($opal.gvars["$:"] = LOADER_PATHS));


($opal.gvars["$~"] = nil);

$const.RUBY_ENGINE = "opal-browser";
$const.RUBY_PLATFORM = "opal";
$const.RUBY_VERSION = "1.9.2";
$const.ARGV = [];

$klass(this, nil, "Module", function() {var $const = this.$const, def = this.$proto; 
  def.$eqq$ = function(object) {

    return object.$kind_of$p(this);};

  def.$alias_method = function(newname, oldname) {
    $opal.alias(this, newname, oldname);

    return this;
  };

  def.$ancestors = function() {

    
      var parent = this,
          result = [];

      while (parent) {
        if (!(parent.$flags & FL_SINGLETON)) {
          result.push(parent);
        }

        parent = parent.$s;
      }

      return result;
    };

  def.$append_features = function(mod) {
    include_module(mod, this);

    return this;
  };

  def.$attr_accessor = function(attrs) {attrs = $slice.call(arguments, 0);

    
      for (var i = 0, length = attrs.length; i < length; i++) {
        define_attr(this, attrs[i], true, true);
      }

      return nil;
    };

  def.$attr_reader = function(attrs) {attrs = $slice.call(arguments, 0);

    
      for (var i = 0, length = attrs.length; i < length; i++) {
        define_attr(this, attrs[i], true, false);
      }

      return nil;
    };

  def.$attr_writer = function(attrs) {attrs = $slice.call(arguments, 0);

    
      for (var i = 0, length = attrs.length; i < length; i++) {
        define_attr(this, attrs[i], false, true);
      }

      return nil;
    };

  def.$attr = function(name, setter) {if (setter === undefined) { setter = false; }
    define_attr(this, name, true, setter);

    return this;
  };

  def.$define_method = $TMP_1 = function(name) {var $yield = $TMP_1.$P;if ($yield) { var $context = $yield.$S, $block_given = true, body = $yield; $TMP_1.$P = null; }else { $yield = $no_proc, body = nil; }

    
      if (body === nil) {
        raise(RubyLocalJumpError, 'no block given');
      }

      define_method(this, mid_to_jsid(name), body);

      return nil;
    };

  def.$include = function(mods) {var mod = nil; mods = $slice.call(arguments, 0);

    
      var i = mods.length - 1, mod;
      while (i >= 0) {
        mod = mods[i];
        mod.$append_features(this);
        mod.$included(this);

        i--;
      }

      return this;
    };


  def.$instance_methods = function() {

    return [];};

  def.$included = function(mod) {
    return nil;};

  def.$module_eval = $TMP_2 = function() {var $yield = $TMP_2.$P;if ($yield) { var $context = $yield.$S, $block_given = true, block = $yield; $TMP_2.$P = null; }else { $yield = $no_proc, block = nil; }

    
      if (block === nil) {
        raise(RubyLocalJumpError, 'no block given');
      }

      return block.call(this, null);
    };

  $opal.alias(this, "class_eval", "module_eval");

  def.$name = function() {

    return this.$name;};

  $opal.alias(this, "public_instance_methods", "instance_methods");

  return $opal.alias(this, "to_s", "name");
}, 0);

$klass(this, nil, "Class", function() {var $const = this.$const, def = this.$proto; 
  $opal.defs(this, '$new', $TMP_3 = function(sup) {var $yield = $TMP_3.$P;if ($yield) { var $context = $yield.$S, $block_given = true, block = $yield; $TMP_3.$P = null; }else { $yield = $no_proc, block = nil; }if (sup === undefined) { sup = $const.Object; }
    
      var klass       = boot_class(sup);
          klass.$name = "AnonClass";

      make_metaclass(klass, sup.$klass);

      sup.$inherited(klass);

      return block !== nil ? block.call(klass, null) : klass;
    
  });

  def.$allocate = function() {

    return new this.$allocator();};

  def.$new = $TMP_4 = function(args) {var obj = nil, _a, _b, _c; var $yield = $TMP_4.$P;if ($yield) { var $context = $yield.$S, $block_given = true, block = $yield; $TMP_4.$P = null; }else { $yield = $no_proc, block = nil; }args = $slice.call(arguments, 0);
    obj = this.$allocate();
    (_a=(_b=obj).$initialize, _a.$P = 
    (_c = block, (typeof(_c) === 'function' || _c == nil ? _c : _c.$to_proc())), _a).apply(_b, args);
    return obj;};

  def.$inherited = function(cls) {
    return nil;};

  return def.$superclass = function() {

    
      var sup = this.$s;

      if (!sup) {
        if (this === RubyObject) {
          return nil;
        }

        raise(RubyRuntimeError, 'uninitialized class');
      }

      return sup;
    };
}, 0);

$klass(this, nil, "Kernel", function() {var $const = this.$const, def = this.$proto; 
  def.$match$ = function(obj) {

    return false;};

  def.$eqq$ = function(other) {

    return this == other;};

  def.$Array = function(object) {var _a; 


    if ((_a = object) !== false && _a !== nil) {} else {return []};
      if (object.$to_ary) {
        return object.$to_ary();
      }
      else if (object.$to_a) {
        return object.$to_a();
      }

      var length = object.length || 0,
          result = [];

      while (length--) {
        result[length] = object[length];
      }

      return result;
    
  };

  def.$at_exit = $TMP_5 = function() {var $yield = $TMP_5.$P;if ($yield) { var $context = $yield.$S, $block_given = true, block = $yield; $TMP_5.$P = null; }else { $yield = $no_proc, block = nil; }

    
      if (block === nil) {
        raise(RubyArgError, 'called without a block');
      }

      end_procs.push(block);

      return block;
    };

  def.$class = function() {

    return class_real(this.$klass);};

  def.$define_singleton_method = $TMP_6 = function() {var $yield = $TMP_6.$P;if ($yield) { var $context = $yield.$S, $block_given = true, body = $yield; $TMP_6.$P = null; }else { $yield = $no_proc, body = nil; }

    
      if (body === nil) {
        raise(RubyLocalJumpError, 'no block given');
      }

      $opal.ds(this, name, body);

      return this;
    };

  def.$equal$p = function(other) {

    return this === other;};

  def.$extend = function(mods) {mods = $slice.call(arguments, 0);

    
      for (var i = 0, length = mods.length; i < length; i++) {
        include_module(singleton_class(this), mods[i]);
      }

      return this;
    };

  def.$hash = function() {

    return this.$id;};

  def.$inspect = function() {

    return this.$to_s();};

  def.$instance_of$p = function(klass) {

    return this.$klass === klass;};

  def.$instance_variable_defined$p = function(name) {

    return hasOwnProperty.call(this, name.substr(1));};

  def.$instance_variable_get = function(name) {

    
      var ivar = this[name.substr(1)];

      return ivar == undefined ? nil : ivar;
    };

  def.$instance_variable_set = function(name, value) {

    return this[name.substr(1)] = value;};

  def.$instance_variables = function() {

    
      var result = [];

      for (var name in this) {
        result.push(name);
      }

      return result;
    };

  def.$is_a$p = function(klass) {

    
      var search = this.$klass;

      while (search) {
        if (search === klass) {
          return true;
        }

        search = search.$s;
      }

      return false;
    };

  $opal.alias(this, "kind_of?", "is_a?");

  def.$lambda = $TMP_7 = function() {var $yield = $TMP_7.$P;if ($yield) { var $context = $yield.$S, $block_given = true, block = $yield; $TMP_7.$P = null; }else { $yield = $no_proc, block = nil; }

    return block;};

  def.$loop = $TMP_8 = function() {var $yield = $TMP_8.$P;if ($yield) { var $context = $yield.$S, $block_given = true, block = $yield; $TMP_8.$P = null; }else { $yield = $no_proc, block = nil; }


    if ($block_given) {} else {return this.$enum_for("loop")};
      while (true) {
        if ($yield.call($context) === breaker) {
          return breaker.$v;
        }
      }

      return this;
    
  };

  def.$nil$p = function() {

    return false;};

  def.$object_id = function() {

    return this.$id || (this.$id = unique_id++);};

  def.$print = function(strs) {var _a, _b; strs = $slice.call(arguments, 0);

    return (_a=((_b = $opal.gvars["$stdout"]) == null ? nil : _b)).$print.apply(_a, strs);};

  def.$proc = $TMP_9 = function() {var $yield = $TMP_9.$P;if ($yield) { var $context = $yield.$S, $block_given = true, block = $yield; $TMP_9.$P = null; }else { $yield = $no_proc, block = nil; }

    return block;};

  def.$puts = function(strs) {var _a, _b; strs = $slice.call(arguments, 0);

    return (_a=((_b = $opal.gvars["$stdout"]) == null ? nil : _b)).$puts.apply(_a, strs);};

  def.$raise = function(exception, string) {var _a; 

    
      if (typeof(exception) === 'string') {
        exception = (RubyRuntimeError).$new(exception);
      }
      else if (((_a = exception.$is_a$p(RubyException)) === false || _a === nil)) {
        exception = (exception).$new(string);
      }

      throw exception;
    };

  def.$rand = function(max) {

    return max === undefined ? Math.random() : Math.floor(Math.random() * max);};

  def.$require = function(path) {

    
      var resolved = find_lib(path);

      if (!resolved) {
        raise(RubyLoadError, 'no such file to load -- ' + path);
      }

      if (LOADER_CACHE[resolved]) {
        return false;
      }

      LOADER_CACHE[resolved] = true;
      $opal.FILE = resolved;
      FACTORIES[resolved]();

      return true;
    };

  def.$respond_to$p = function(name) {

    return !!this[mid_to_jsid(name)];};

  def.$singleton_class = function() {

    return singleton_class(this);};

  def.$tap = $TMP_10 = function() {var $yield = $TMP_10.$P;if ($yield) { var $context = $yield.$S, $block_given = true, block = $yield; $TMP_10.$P = null; }else { $yield = $no_proc, block = nil; }

    
      if (block === nil) {
        raise(RubyLocalJumpError, 'no block given');
      }

      if ($yield.call($context, this) === breaker) {
        return breaker.$v;
      }

      return this;
    };

  def.$to_s = function() {

    return inspect_object(this);};;this.$donate(["$match$", "$eqq$", "$Array", "$at_exit", "$class", "$define_singleton_method", "$equal$p", "$extend", "$hash", "$inspect", "$instance_of$p", "$instance_variable_defined$p", "$instance_variable_get", "$instance_variable_set", "$instance_variables", "$is_a$p", "$lambda", "$loop", "$nil$p", "$object_id", "$print", "$proc", "$puts", "$raise", "$rand", "$require", "$respond_to$p", "$singleton_class", "$tap", "$to_s"]);
}, 1);

$klass(this, nil, "BasicObject", function() {var $const = this.$const, def = this.$proto; 
  def.$initialize = function() {
    return nil;};

  def.$eq$ = function(other) {

    return this === other;};

  def.$__send__ = $TMP_11 = function(symbol, args) {var $yield = $TMP_11.$P;if ($yield) { var $context = $yield.$S, $block_given = true, block = $yield; $TMP_11.$P = null; }else { $yield = $no_proc, block = nil; }args = $slice.call(arguments, 1);

    
      var meth = this[mid_to_jsid(symbol)] || $opal.mm(mid_to_jsid(symbol));

      return meth.apply(this, args);
    };

  $opal.alias(this, "send", "__send__");

  $opal.alias(this, "eql?", "==");
  $opal.alias(this, "equal?", "==");

  def.$instance_eval = $TMP_12 = function(string) {var $yield = $TMP_12.$P;if ($yield) { var $context = $yield.$S, $block_given = true, block = $yield; $TMP_12.$P = null; }else { $yield = $no_proc, block = nil; }if (string === undefined) { string = nil; }

    
      if (block === nil) {
        raise(RubyArgError, 'block not supplied');
      }

      return block.call(this, this);
    };

  def.$instance_exec = $TMP_13 = function(args) {var $yield = $TMP_13.$P;if ($yield) { var $context = $yield.$S, $block_given = true, block = $yield; $TMP_13.$P = null; }else { $yield = $no_proc, block = nil; }args = $slice.call(arguments, 0);

    
      if (block === nil) {
        raise(RubyArgError, 'block not supplied');
      }

      return block.apply(this, args);
    };

  def.$method_missing = function(symbol, args) {args = $slice.call(arguments, 1);

    return raise(RubyNoMethodError, 'undefined method `' + symbol + '` for ' + this.$inspect());};

  def.$singleton_method_added = function(symbol) {
    return nil;};

  def.$singleton_method_removed = function(symbol) {
    return nil;};

  def.$singleton_method_undefined = function(symbol) {
    return nil;};;this.$donate(["$initialize", "$eq$", "$__send__", "$instance_eval", "$instance_exec", "$method_missing", "$singleton_method_added", "$singleton_method_removed", "$singleton_method_undefined"]);
}, 0);

$klass(this, nil, "Object", function() {var $const = this.$const, def = this.$proto; 


  this.$include($const.Kernel);
  def.$methods = function() {

    return [];};

  $opal.alias(this, "private_methods", "methods");
  $opal.alias(this, "protected_methods", "methods");
  $opal.alias(this, "public_methods", "methods");


  def.$singleton_methods = function() {

    return [];};;this.$donate(["$methods", "$singleton_methods"]);
}, 0);

$opal.defs(this, '$to_s', function(
  ) {return "main"
});

$opal.defs(this, '$include', function(mod) {
  return $const.Object.$include(
  mod)});

$klass(this, nil, "Boolean", function() {var $const = this.$const, def = this.$proto; 
  def.$and$ = function(other) {

    return (this == true) ? (other !== false && other !== nil) : false;};

  def.$or$ = function(other) {

    return (this == true) ? true : (other !== false && other !== nil);};

  def.$xor$ = function(other) {

    return (this == true) ? (other === false || other === nil) : (other !== false && other !== nil);};

  def.$eq$ = function(other) {

    return (this == true) === other.valueOf();};

  def.$class = function() {

    return (this == true) ? $const.TrueClass : $const.FalseClass;};

  return def.$to_s = function() {

    return (this == true) ? 'true' : 'false';};
}, 0);

$klass(this, nil, "TrueClass", function() {var $const = this.$const, def = this.$proto; 
  return $opal.defs(this, '$eqq$', function(obj) {
    return obj === true;
  })
}, 0);

$klass(this, nil, "FalseClass", function() {var $const = this.$const, def = this.$proto; 
  return $opal.defs(this, '$eqq$', function(obj) {
    return obj === false;
  })
}, 0);

$const.TRUE = true;
$const.FALSE = false;

$klass(this, nil, "NilClass", function() {var $const = this.$const, def = this.$proto; 
  def.$and$ = function(other) {

    return false;};

  def.$or$ = function(other) {

    return other !== false && other !== nil;};

  def.$xor$ = function(other) {

    return other !== false && other !== nil;};

  def.$eq$ = function(other) {

    return this === other;};

  def.$inspect = function() {

    return "nil";};

  def.$nil$p = function() {

    return true;};

  def.$to_a = function() {

    return [];};

  def.$to_i = function() {

    return 0;};

  $opal.alias(this, "to_f", "to_i");

  return def.$to_s = function() {

    return "";};
}, 0);

$const.NIL = nil;

$klass(this, nil, "Enumerable", function() {var $const = this.$const, def = this.$proto; 
  def.$all$p = $TMP_14 = function() {var $yield = $TMP_14.$P;if ($yield) { var $context = $yield.$S, $block_given = true, block = $yield; $TMP_14.$P = null; }else { $yield = $no_proc, block = nil; }

    
      var result = true;

      this.$each.$P = block !== nil
        ? function(obj) {
            var value;

            if ((value = $yield.call($context, obj)) === $breaker) {
              return $breaker.$v;
            }

            if (value === false || value === nil) {
              result      = false;
              $breaker.$v = nil;

              return $breaker;
            }
          }
        : function(obj) {
            if (obj === false || obj === nil) {
              result      = false;
              $breaker.$v = nil;

              return $breaker;
            }
          };

      this.$each();

      return result;
    };

  def.$any$p = $TMP_15 = function() {var $yield = $TMP_15.$P;if ($yield) { var $context = $yield.$S, $block_given = true, block = $yield; $TMP_15.$P = null; }else { $yield = $no_proc, block = nil; }

    
      var result = false;

      this.$each.$P = block !== nil
        ? function(obj) {
            var value;

            if ((value = $yield.call($context, obj)) === $breaker) {
              return $breaker.$v;
            }

            if (value !== false && value !== nil) {
              result      = true;
              $breaker.$v = nil;

              return $breaker;
            }
          }
        : function(obj) {
            if (obj !== false && obj !== nil) {
              result      = true;
              $breaker.$v = nil;

              return $breaker;
            }
          };

      this.$each();

      return result;
    };

  def.$collect = $TMP_16 = function() {var $yield = $TMP_16.$P;if ($yield) { var $context = $yield.$S, $block_given = true, block = $yield; $TMP_16.$P = null; }else { $yield = $no_proc, block = nil; }


    if ($block_given) {} else {return this.$enum_for("collect")};
      var result = [];

      this.$each.$P = function () {
        var obj = $slice.call(arguments),
            value;

        if ((value = $yield.apply($context, obj)) === $breaker) {
          return $breaker.$v;
        }

        result.push(value);
      };

      this.$each();

      return result;
    
  };

  def.$count = $TMP_17 = function(object) {var $yield = $TMP_17.$P;if ($yield) { var $context = $yield.$S, $block_given = true, block = $yield; $TMP_17.$P = null; }else { $yield = $no_proc, block = nil; }

    
      var result = 0;

      if (block === nil) {
        if (object === undefined) {
          $yield = function() { return true; };
        }
        else {
          $yield = function(obj) { return (obj).$eq$(object); };
        }
      }

      this.$each.$P = function(obj) {
        var value;

        if ((value = $yield.call($context, obj)) === $breaker) {
          return $breaker.$v;
        }

        if (value !== false && value !== nil) {
          result++;
        }
      };

      this.$each();

      return result;
    };

  def.$detect = $TMP_18 = function(ifnone) {var _a; var $yield = $TMP_18.$P;if ($yield) { var $context = $yield.$S, $block_given = true, block = $yield; $TMP_18.$P = null; }else { $yield = $no_proc, block = nil; }


    if ((_a = block) !== false && _a !== nil) {} else {return this.$enum_for("detect", ifnone)};
      var result = nil;

      this.$each.$P = function(obj) {
        var value;

        if ((value = $yield.call($context, obj)) === $breaker) {
          return $breaker.$v;
        }

        if (value !== false && value !== nil) {
          result      = obj;
          $breaker.$v = nil;

          return $breaker;
        }
      };

      this.$each();

      if (result !== nil) {
        return result;
      }

      if (typeof(ifnone) === 'function') {
        return ifnone.$call();
      }

      return ifnone === undefined ? nil : ifnone;
    
  };

  def.$drop = function(number) {


    this.$raise($const.NotImplementedError);
      var result  = [],
          current = 0;

      this.$each.$P = function(obj) {
        if (number < current) {
          result.push(e);
        }

        current++;
      };

      this.$each();

      return result;
    
  };

  def.$drop_while = $TMP_19 = function() {var _a; var $yield = $TMP_19.$P;if ($yield) { var $context = $yield.$S, $block_given = true, block = $yield; $TMP_19.$P = null; }else { $yield = $no_proc, block = nil; }


    if ((_a = block) !== false && _a !== nil) {} else {return this.$enum_for("drop_while")};
      var result = [];

      this.$each.$P = function(obj) {
        var value;

        if ((value = $yield.call($context, obj)) === $breaker) {
          return $breaker.$v;
        }

        if (value !== false && value !== nil) {
          result.push(obj);
        }
        else {
          return $breaker;
        }
      };

      this.$each();

      return result;
    
  };

  def.$each_with_index = $TMP_20 = function() {var _a; var $yield = $TMP_20.$P;if ($yield) { var $context = $yield.$S, $block_given = true, block = $yield; $TMP_20.$P = null; }else { $yield = $no_proc, block = nil; }


    if ((_a = block) !== false && _a !== nil) {} else {return this.$enum_for("each_with_index")};
      var index = 0;

      this.$each.$P = function(obj) {
        var value;

        if ((value = $yield.call($context, obj, index)) === $breaker) {
          return $breaker.$v;
        }

        index++;
      };

      this.$each();

      return nil;
    
  };

  def.$entries = function() {

    
      var result = [];

      this.$each.$P = function(obj) { return result.push(obj); };
      this.$each();

      return result;
    };

  $opal.alias(this, "find", "detect");

  def.$find_index = $TMP_21 = function(object) {var _a; var $yield = $TMP_21.$P;if ($yield) { var $context = $yield.$S, $block_given = true, block = $yield; $TMP_21.$P = null; }else { $yield = $no_proc, block = nil; }


    if ((_a = block) !== false && _a !== nil) {} else {return this.$enum_for("find_index", object)};
      if (object !== undefined) {
        $yield = function (iter, obj) { return obj.$eq$(object); };
      }

      var result = nil;

      this.$each_with_index.$P = function(obj, index) {
        var value;

        if ((value = $yield.call($context, obj)) === $breaker) {
          return $breaker.$v;
        }

        if (value !== false && value !== nil) {
          result     = obj;
          breaker.$v = index;

          return $breaker;
        }
      };

      this.$each_with_index();

      return result;
    
  };

  def.$first = function(number) {

    
      var result = [],
          current = 0;

      this.$each.$P = number === undefined
        ? function(obj) {
            result = obj; return $breaker;
          }
        : function(obj) {
            if (number <= current) {
              return $breaker;
            }

            result.push(obj);

            current++;
          };

      this.$each();

      return result;
    };

  def.$grep = $TMP_22 = function(pattern) {var $yield = $TMP_22.$P;if ($yield) { var $context = $yield.$S, $block_given = true, block = $yield; $TMP_22.$P = null; }else { $yield = $no_proc, block = nil; }

    
      var result = [];

      this.$each.$P = block !== nil
        ? function(obj) {
            var value = pattern.$eqq$(obj);

            if (value !== false && value !== nil) {
              if ((value = $yield.call($context, obj)) === $breaker) {
                return $breaker.$v;
              }

              result.push(obj);
            }
          }
        : function(obj) {
            var value = pattern.$eqq$(obj);

            if (value !== false && value !== nil) {
              ary.push(obj);
            }
          };

      this.$each();

      return result;
    };

  $opal.alias(this, "take", "first");

  $opal.alias(this, "to_a", "entries");;this.$donate(["$all$p", "$any$p", "$collect", "$count", "$detect", "$drop", "$drop_while", "$each_with_index", "$entries", "$find_index", "$first", "$grep"]);
}, 1);

$klass(this, nil, "Enumerator", function() {var $const = this.$const, def = this.$proto; 


  this.$include($const.Enumerable);$klass(this, nil, "Yielder", function() {var $const = this.$const, def = this.$proto; 
    def.$initialize = function(block) {

      return this.block = block;};

    def.$call = function(block) {this.block == null && (this.block = nil);
      this.call = 

      block;return this.block.$call();
    };

    def.$yield = function(value) {this.call == null && (this.call = nil);

      return this.call.$call(value);};

    return $opal.alias(this, "<<", "yield");
  }, 0);

  $klass(this, nil, "Generator", function() {var $const = this.$const, def = this.$proto; 
    this.$attr_reader("enumerator");

    def.$initialize = function(block) {

      return this.yielder = $const.Yielder.$new(block);};

    return def.$each = $TMP_23 = function() {this.yielder == null && (this.yielder = nil);var $yield = $TMP_23.$P;if ($yield) { var $context = $yield.$S, $block_given = true, block = $yield; $TMP_23.$P = null; }else { $yield = $no_proc, block = nil; }

      return this.yielder.$call(block);};
  }, 0);

  def.$initialize = $TMP_24 = function(object, method, args) {var _a; var $yield = $TMP_24.$P;if ($yield) { var $context = $yield.$S, $block_given = true, block = $yield; $TMP_24.$P = null; }else { $yield = $no_proc, block = nil; }if (object === undefined) { object = nil; }if (method === undefined) { method = "each"; }args = $slice.call(arguments, 2);

    if ($block_given) {this.object = $const.Generator.$new(block)
    };



    if ((_a = object) !== false && _a !== nil) {} else {this.$raise($const.ArgumentError, "wrong number of argument (0 for 1+)")};this.object = 
    object;this.method = 
    method;return this.args = 
    args;};

  def.$next = function() {var result = nil, _a, _b; this.cache == null && (this.cache = nil);this.current == null && (this.current = nil);


    this.$_init_cache();(_a = result = this.cache.$aref$(this.current), _a !== false && _a != nil ? _a : this.$raise($const.StopIteration, "iteration reached an end"));
    this.current = (_a = this.current, _b = 1, typeof(_a) === 'number' ? _a + _b : _a.$plus$(_b));


    return result;};

  def.$next_values = function() {var result = nil, _a; 
    result = this.$next();

    if ((_a = result.$is_a$p($const.Array)) !== false && _a !== nil) {return result} else {return [result]};
  };

  def.$peek = function() {var _a; this.cache == null && (this.cache = nil);this.current == null && (this.current = nil);


    this.$_init_cache();return (_a = this.cache.$aref$(this.current), _a !== false && _a != nil ? _a : this.$raise($const.StopIteration, "iteration reached an end"));
  };

  def.$peel_values = function() {var result = nil, _a; 
    result = this.$peek();

    if ((_a = result.$is_a$p($const.Array)) !== false && _a !== nil) {return result} else {return [result]};
  };

  def.$rewind = function() {

    return this.$_clear_cache();};

  def.$each = $TMP_25 = function() {var _a, _b, _c; this.object == null && (this.object = nil);this.method == null && (this.method = nil);var $yield = $TMP_25.$P;if ($yield) { var $context = $yield.$S, $block_given = true, block = $yield; $TMP_25.$P = null; }else { $yield = $no_proc, block = nil; }


    if ((_a = block) !== false && _a !== nil) {} else {return this};return (_a=(_b=this.object).$__send__, _a.$P = 
    (_c = block, (typeof(_c) === 'function' || _c == nil ? _c : _c.$to_proc())), _a).apply(_b, [this.method].concat(this.$args()));};

  def.$each_with_index = $TMP_26 = function() {var _a, _b, _c; var $yield = $TMP_26.$P;if ($yield) { var $context = $yield.$S, $block_given = true, block = $yield; $TMP_26.$P = null; }else { $yield = $no_proc, block = nil; }

    return (_a=(_b=this).$with_index, _a.$P = (_c = block, (typeof(_c) === 'function' || _c == nil ? _c : _c.$to_proc())), _a).call(_b);};

  def.$with_index = $TMP_27 = function(offset) {var current = nil, _a, _b; var $yield = $TMP_27.$P;if ($yield) { var $context = $yield.$S, $block_given = true; $TMP_27.$P = null; }else { $yield = $no_proc; }if (offset === undefined) { offset = 0; }


    if ($block_given) {} else {return $const.Enumerator.$new(this, "with_index", offset)};current = 0;

    return (_a=(_b=this).$each, (_a.$P = function(args) {var _a, _b; args = $slice.call(arguments, 0);
      if ((_a = current, _b = 

      offset, typeof(_a) === 'number' ? _a >= _b : _a.$ge$(_b))) {} else {return nil;};

      $yield.apply($context, args.concat([["current"]]));return current = (_b = current, _a = 1, typeof(_b) === 'number' ? _b + _a : _b.$plus$(_a));
    }).$S = this, _a).call(_b);
  };

  def.$with_object = $TMP_28 = function(object) {var _a, _b; try {var $yield = $TMP_28.$P;if ($yield) { var $context = $yield.$S, $block_given = true; $TMP_28.$P = null; }else { $yield = $no_proc; }


    if ($block_given) {} else {return $const.Enumerator.$new(this, "with_object", object)};return (_a=(_b=this).$each, (_a.$P = function(args) {var _a; args = $slice.call(arguments, 0);

      return ((_a = $yield.apply($context, args.concat([["object"]]))) === $breaker ? _a.$t() : _a)}).$S = this, _a).call(_b);} catch (e) { if (e === $breaker) { return e.$v; }; throw e;}
  };

  def.$_init_cache = function() {var _a; this.current == null && (this.current = nil);this.cache == null && (this.cache = nil);
    (_a = this.current, _a !== false && _a != nil ? _a : this.current = 0);
    return (_a = this.cache, _a !== false && _a != nil ? _a : this.cache = 
    this.$to_a());};

  return def.$_clear_cache = function() {
    this.cache = nil;
    return this.current = nil;
  };
}, 0);

$klass(this, nil, "Kernel", function() {var $const = this.$const, def = this.$proto; 
  def.$enum_for = function(method, args) {var _a; if (method === undefined) { method = "each"; }args = $slice.call(arguments, 1);

    return (_a=$const.Enumerator).$new.apply(_a, [this, method].concat(args));};

  $opal.alias(this, "to_enum", "enum_for");;this.$donate(["$enum_for"]);
}, 1);

$klass(this, nil, "Comparable", function() {var $const = this.$const, def = this.$proto; 
  def.$lt$ = function(other) {

    return this.$cmp$(other).$eq$(-1);};

  def.$le$ = function(other) {var _a, _b; 

    return (_a = this.$cmp$(other), _b = 0, typeof(_a) === 'number' ? _a <= _b : _a.$le$(_b));};

  def.$eq$ = function(other) {

    return this.$cmp$(other).$eq$(0);};

  def.$gt$ = function(other) {

    return this.$cmp$(other).$eq$(1);};

  def.$ge$ = function(other) {var _a, _b; 

    return (_a = this.$cmp$(other), _b = 0, typeof(_a) === 'number' ? _a >= _b : _a.$ge$(_b));};

  def.$between$p = function(min, max) {var _a, _b, _c; 

    return (_a = (_b = this, _c = min, typeof(_b) === 'number' ? _b > _c : _b.$gt$(_c)) ? (_c = this, _b = max, typeof(_c) === 'number' ? _c < _b : _c.$lt$(_b)) : _a);};;this.$donate(["$lt$", "$le$", "$eq$", "$gt$", "$ge$", "$between$p"]);
}, 1);

$klass(this, nil, "Array", function() {var $const = this.$const, def = this.$proto; 


  this.$include($const.Enumerable);$opal.defs(this, '$aref$', function(objects) {objects = $slice.call(arguments, 0);
    
      var result = this.$allocate();

      result.splice.apply(result, [0, 0].concat(objects));

      return result;
    
  });

  $opal.defs(this, '$allocate', function(
    ) {
      var array        = [];
          array.$klass = this;

      return array;
    
  });

  $opal.defs(this, '$new', function(a) {a = $slice.call(arguments, 0);
    return [];
  });

  def.$and$ = function(other) {

    
      var result = [],
          seen   = {};

      for (var i = 0, length = this.length; i < length; i++) {
        var item = this[i],
            hash = item;

        if (!seen[hash]) {
          for (var j = 0, length2 = other.length; j < length2; j++) {
            var item2 = other[j],
                hash2 = item2;

            if ((hash === hash2) && !seen[hash]) {
              seen[hash] = true;

              result.push(item);
            }
          }
        }
      }

      return result;
    };

  def.$mul$ = function(other) {

    
      if (typeof(other) === 'string') {
        return this.join(other);
      }

      var result = [];

      for (var i = 0, length = this.length; i < length; i++) {
        result = result.concat(this);
      }

      return result;
    };

  def.$plus$ = function(other) {

    return this.slice(0).concat(other.slice(0));};

  def.$lshft$ = function(object) {
    this.push(object);

    return this;
  };

  def.$cmp$ = function(other) {

    
      if (this.$hash() === other.$hash()) {
        return 0;
      }

      if (this.length != other.length) {
        return (this.length > other.length) ? 1 : -1;
      }

      for (var i = 0, length = this.length, tmp; i < length; i++) {
        if ((tmp = (this[i]).$cmp$(other[i])) !== 0) {
          return tmp;
        }
      }

      return 0;
    };

  def.$eq$ = function(other) {

    
      if (this.length !== other.length) {
        return false;
      }

      for (var i = 0, length = this.length; i < length; i++) {
        if (!(this[i]).$eq$(other[i])) {
          return false;
        }
      }

      return true;
    };


  def.$aref$ = function(index, length) {

    
      var size = this.length;

      if (index < 0) {
        index += size;
      }

      if (length !== undefined) {
        if (length < 0 || index > size || index < 0) {
          return nil;
        }

        return this.slice(index, index + length);
      }
      else {
        if (index >= size || index < 0) {
          return nil;
        }

        return this[index];
      }
    };


  def.$aset$ = function(index, value) {

    
      var size = this.length;

      if (index < 0) {
        index += size;
      }

      return this[index] = value;
    };

  def.$assoc = function(object) {

    
      for (var i = 0, length = this.length, item; i < length; i++) {
        if (item = this[i], item.length && (item[0]).$eq$(object)) {
          return item;
        }
      }

      return nil;
    };

  def.$at = function(index) {

    
      if (index < 0) {
        index += this.length;
      }

      if (index < 0 || index >= this.length) {
        return nil;
      }

      return this[index];
    };

  def.$clear = function() {
    this.splice(0);

    return this;
  };

  def.$clone = function() {

    return this.slice(0);};

  def.$collect = $TMP_29 = function() {var $yield = $TMP_29.$P;if ($yield) { var $context = $yield.$S, $block_given = true, block = $yield; $TMP_29.$P = null; }else { $yield = $no_proc, block = nil; }


    if ($block_given) {} else {return this.$enum_for("collect")};
      var result = [];

      for (var i = 0, length = this.length, value; i < length; i++) {
        if ((value = $yield.call($context, this[i])) === $breaker) {
          return $breaker.$v;
        }

        result.push(value);
      }

      return result;
    
  };

  def.$collect$b = $TMP_30 = function() {var $yield = $TMP_30.$P;if ($yield) { var $context = $yield.$S, $block_given = true, block = $yield; $TMP_30.$P = null; }else { $yield = $no_proc, block = nil; }


    if ($block_given) {} else {return this.$enum_for("collect!")};
      for (var i = 0, length = this.length, val; i < length; i++) {
        if ((val = $yield.call($context, this[i])) === $breaker) {
          return $breaker.$v;
        }

        this[i] = val;
      }
    

    return this;
  };

  def.$compact = function() {

    
      var result = [];

      for (var i = 0, length = this.length, item; i < length; i++) {
        if ((item = this[i]) !== nil) {
          result.push(item);
        }
      }

      return result;
    };

  def.$compact$b = function() {

    
      var original = this.length;

      for (var i = 0, length = this.length; i < length; i++) {
        if (this[i] === nil) {
          this.splice(i, 1);

          length--;
          i--;
        }
      }

      return this.length === original ? nil : this;
    };

  def.$concat = function(other) {
    
      for (var i = 0, length = other.length; i < length; i++) {
        this.push(other[i]);
      }
    

    return this;
  };

  def.$count = function(object) {

    
      if (object === undefined) {
        return this.length;
      }

      var result = 0;

      for (var i = 0, length = this.length; i < length; i++) {
        if ((this[i]).$eq$(object)) {
          result++;
        }
      }

      return result;
    };

  def.$delete = function(object) {

    
      var original = this.length;

      for (var i = 0, length = original; i < length; i++) {
        if ((this[i]).$eq$(object)) {
          this.splice(i, 1);

          length--;
          i--;
        }
      }

      return this.length === original ? nil : object;
    };

  def.$delete_at = function(index) {

    
      if (index < 0) {
        index += this.length;
      }

      if (index < 0 || index >= this.length) {
        return nil;
      }

      var result = this[index];

      this.splice(index, 1);

      return result;
    };

  def.$delete_if = $TMP_31 = function() {var $yield = $TMP_31.$P;if ($yield) { var $context = $yield.$S, $block_given = true, block = $yield; $TMP_31.$P = null; }else { $yield = $no_proc, block = nil; }


    if ($block_given) {} else {return this.$enum_for("delete_if")};
      for (var i = 0, length = this.length, value; i < length; i++) {
        if ((value = $yield.call($context, this[i])) === $breaker) {
          return $breaker.$v;
        }

        if (value !== false && value !== nil) {
          this.splice(i, 1);

          length--;
          i--;
        }
      }
    

    return this;
  };

  def.$drop = function(number) {

    return this.slice(number);};

  def.$drop_while = $TMP_32 = function() {var $yield = $TMP_32.$P;if ($yield) { var $context = $yield.$S, $block_given = true, block = $yield; $TMP_32.$P = null; }else { $yield = $no_proc, block = nil; }


    if ($block_given) {} else {return this.$enum_for("drop_while")};
      for (var i = 0, length = this.length, value; i < length; i++) {
        if ((value = $yield.call($context, this[i])) === $breaker) {
          return $breaker.$v;
        }

        if (value === false || value === nil) {
          return this.slice(i);
        }
      }

      return [];
    
  };

  def.$each = $TMP_33 = function() {var $yield = $TMP_33.$P;if ($yield) { var $context = $yield.$S, $block_given = true, block = $yield; $TMP_33.$P = null; }else { $yield = $no_proc, block = nil; }


    if ($block_given) {} else {return this.$enum_for("each")};
      for (var i = 0, length = this.length; i < length; i++) {
        if ($yield.call($context, this[i]) === $breaker) {
          return $breaker.$v;
        }
      }
    

    return this;
  };

  def.$each_index = $TMP_34 = function() {var $yield = $TMP_34.$P;if ($yield) { var $context = $yield.$S, $block_given = true, block = $yield; $TMP_34.$P = null; }else { $yield = $no_proc, block = nil; }


    if ($block_given) {} else {return this.$enum_for("each_index")};
      for (var i = 0, length = this.length; i < length; i++) {
        if ($yield.call($context, i) === $breaker) {
          return $breaker.$v;
        }
      }
    

    return this;
  };

  def.$each_with_index = $TMP_35 = function() {var $yield = $TMP_35.$P;if ($yield) { var $context = $yield.$S, $block_given = true, block = $yield; $TMP_35.$P = null; }else { $yield = $no_proc, block = nil; }


    if ($block_given) {} else {return this.$enum_for("each_with_index")};
      for (var i = 0, length = this.length; i < length; i++) {
        if ($yield.call($context, this[i], i) === $breaker) {
          return $breaker.$v;
        }
      }
    

    return this;
  };

  def.$empty$p = function() {

    return this.length === 0;};

  def.$fetch = $TMP_36 = function(index, defaults) {var $yield = $TMP_36.$P;if ($yield) { var $context = $yield.$S, $block_given = true, block = $yield; $TMP_36.$P = null; }else { $yield = $no_proc, block = nil; }

    
      var original = index;

      if (index < 0) {
        index += this.length;
      }

      if (index >= 0 && index < this.length) {
        return this[index];
      }

      if (defaults !== undefined) {
        return defaults;
      }

      if (block !== nil) {
        return $yield.call($context, original);
      }

      raise(RubyIndexError, 'Array#fetch');
    };

  def.$first = function(count) {

    
      if (count !== undefined) {
        return this.slice(0, count);
      }

      return this.length === 0 ? nil : this[0];
    };

  def.$flatten = function(level) {

    
      var result = [];

      for (var i = 0, length = this.length, item; i < length; i++) {
        item = this[i];

        if (item.$flags & T_ARRAY) {
          if (level === undefined) {
            result = result.concat((item).$flatten());
          }
          else if (level === 0) {
            result.push(item);
          }
          else {
            result = result.concat((item).$flatten(level - 1));
          }
        }
        else {
          result.push(item);
        }
      }

      return result;
    };

  def.$flatten$b = function(level) {

    
      var size = this.length;
      this.$replace(this.$flatten(level));

      return size === this.length ? nil : this;
    };

  def.$grep = function(pattern) {

    
      var result = [];

      for (var i = 0, length = this.length, item; i < length; i++) {
        item = this[i];

        if (pattern.$eqq$(item)) {
          result.push(item);
        }
      }

      return result;
    };

  def.$hash = function() {

    return this.$id || (this.$id = unique_id++);};

  def.$include$p = function(member) {

    
      for (var i = 0, length = this.length; i < length; i++) {
        if ((this[i]).$eq$(member)) {
          return true;
        }
      }

      return false;
    };

  def.$index = $TMP_37 = function(object) {var _a, _b; var $yield = $TMP_37.$P;if ($yield) { var $context = $yield.$S, $block_given = true, block = $yield; $TMP_37.$P = null; }else { $yield = $no_proc, block = nil; }
    if ((_a = (_b = $block_given ? object.$eq$(

    undefined) : _b)) !== false && _a !== nil) {} else {return this.$enum_for("index")};
      if (block !== nil) {
        for (var i = 0, length = this.length, value; i < length; i++) {
          if ((value = $yield.call($context, this[i])) === $breaker) {
            return $breaker.$v;
          }

          if (value !== false && value !== nil) {
            return i;
          }
        }
      }
      else {
        for (var i = 0, length = this.length; i < length; i++) {
          if ((this[i]).$eq$(object)) {
            return i;
          }
        }
      }

      return nil
    
  };

  def.$inject = $TMP_38 = function(initial) {var $yield = $TMP_38.$P;if ($yield) { var $context = $yield.$S, $block_given = true, block = $yield; $TMP_38.$P = null; }else { $yield = $no_proc, block = nil; }


    if ($block_given) {} else {return this.$enum_for("inject")};
      var result, i;

      if (initial === undefined) {
        result = this[0];
        i      = 1;
      }
      else {
        result = initial;
        i      = 0;
      }

      for (var length = this.length, value; i < length; i++) {
        if ((value = $yield.call($context, result, this[i])) === $breaker) {
          return $breaker.$v;
        }

        result = value;
      }

      return result;
    
  };

  def.$insert = function(index, objects) {objects = $slice.call(arguments, 1);
    
      if (objects.length > 0) {
        if (index < 0) {
          index += this.length + 1;

          if (index < 0) {
            raise(RubyIndexError, index + ' is out of bounds');
          }
        }
        if (index > this.length) {
          for (var i = this.length; i < index; i++) {
            this.push(nil);
          }
        }

        this.splice.apply(this, [index, 0].concat(objects));
      }
    

    return this;
  };

  def.$inspect = function() {

    
      var inspect = [];

      for (var i = 0, length = this.length; i < length; i++) {
        inspect.push((this[i]).$inspect());
      }

      return '[' + inspect.join(', ') + ']';
    };

  def.$join = function(sep) {if (sep === undefined) { sep = ""; }

    
      var result = [];

      for (var i = 0, length = this.length; i < length; i++) {
        result.push((this[i]).$to_s());
      }

      return result.join(sep);
    };

  def.$keep_if = $TMP_39 = function() {var $yield = $TMP_39.$P;if ($yield) { var $context = $yield.$S, $block_given = true, block = $yield; $TMP_39.$P = null; }else { $yield = $no_proc, block = nil; }

    if ($block_given) {} else {return this.$enum_for("keep_if")};
      for (var i = 0, length = this.length, value; i < length; i++) {
        if ((value = $yield.call($context, this[i])) === $breaker) {
          return $breaker.$v;
        }

        if (value === false || value === nil) {
          this.splice(i, 1);

          length--;
          i--;
        }
      }
    

    return this;
  };

  def.$last = function(count) {

    
      var length = this.length;

      if (count === undefined) {
        return length === 0 ? nil : this[length - 1];
      }
      else if (count < 0) {
        raise(RubyArgError, 'negative count given');
      }

      if (count > length) {
        count = length;
      }

      return this.slice(length - count, length);
    };

  def.$length = function() {

    return this.length;};

  $opal.alias(this, "map", "collect");

  $opal.alias(this, "map!", "collect!");

  def.$pop = function(count) {

    
      var length = this.length;

      if (count === undefined) {
        return length === 0 ? nil : this.pop();
      }

      if (count < 0) {
        raise(RubyArgError, 'negative count given');
      }

      return count > length ? this.splice(0) : this.splice(length - count, length);
    };

  def.$push = function(objects) {objects = $slice.call(arguments, 0);
    
      for (var i = 0, length = objects.length; i < length; i++) {
        this.push(objects[i]);
      }
    

    return this;
  };

  def.$rassoc = function(object) {

    
      for (var i = 0, length = this.length, item; i < length; i++) {
        item = this[i];

        if (item.length && item[1] !== undefined) {
          if ((item[1]).$eq$(object)) {
            return item;
          }
        }
      }

      return nil;
    };

  def.$reject = $TMP_40 = function() {var $yield = $TMP_40.$P;if ($yield) { var $context = $yield.$S, $block_given = true, block = $yield; $TMP_40.$P = null; }else { $yield = $no_proc, block = nil; }


    if ($block_given) {} else {return this.$enum_for("reject")};
      var result = [];

      for (var i = 0, length = this.length, value; i < length; i++) {
        if ((value = $yield.call($context, this[i])) === $breaker) {
          return $breaker.$v;
        }

        if (value === false || value === nil) {
          result.push(this[i]);
        }
      }
      return result;
    
  };

  def.$reject$b = $TMP_41 = function() {var $yield = $TMP_41.$P;if ($yield) { var $context = $yield.$S, $block_given = true, block = $yield; $TMP_41.$P = null; }else { $yield = $no_proc, block = nil; }


    if ($block_given) {} else {return this.$enum_for("reject!")};
      var original = this.length;

      for (var i = 0, length = this.length, value; i < length; i++) {
        if ((value = $yield.call($context, this[i])) === $breaker) {
          return $breaker.$v;
        }

        if (value !== false && value !== nil) {
          this.splice(i, 1);

          length--;
          i--;
        }
      }

      return original === this.length ? nil : this;
    
  };

  def.$replace = function(other) {

    
      this.splice(0);
      this.push.apply(this, other);
      return this;
    };

  def.$reverse = function() {

    return this.reverse();};

  def.$reverse$b = function() {

    
      this.splice(0);
      this.push.apply(this, this.$reverse());
      return this;
    };

  def.$reverse_each = $TMP_42 = function() {var _a, _b, _c; var $yield = $TMP_42.$P;if ($yield) { var $context = $yield.$S, $block_given = true, block = $yield; $TMP_42.$P = null; }else { $yield = $no_proc, block = nil; }


    if ($block_given) {} else {return this.$enum_for("reverse_each")};(_a=(_b=this.$reverse()).$each, _a.$P = 

    (_c = block, (typeof(_c) === 'function' || _c == nil ? _c : _c.$to_proc())), _a).call(_b);return this;
  };

  def.$rindex = $TMP_43 = function(object) {var _a, _b; var $yield = $TMP_43.$P;if ($yield) { var $context = $yield.$S, $block_given = true, block = $yield; $TMP_43.$P = null; }else { $yield = $no_proc, block = nil; }
    if ((_a = (_b = $block_given ? object.$eq$(

    undefined) : _b)) !== false && _a !== nil) {} else {return this.$enum_for("rindex")};
      if (block !== nil) {
        for (var i = this.length - 1, value; i >= 0; i--) {
          if ((value = $yield.call($context, this[i])) === $breaker) {
            return $breaker.$v;
          }

          if (value !== false && value !== nil) {
            return i;
          }
        }
      }
      else {
        for (var i = this.length - 1; i >= 0; i--) {
          if ((this[i]).$eq$(object)) {
            return i;
          }
        }
      }

      return nil;
    
  };

  def.$select = $TMP_44 = function() {var $yield = $TMP_44.$P;if ($yield) { var $context = $yield.$S, $block_given = true, block = $yield; $TMP_44.$P = null; }else { $yield = $no_proc, block = nil; }


    if ($block_given) {} else {return this.$enum_for("select")};
      var result = [];

      for (var i = 0, length = this.length, item, value; i < length; i++) {
        item = this[i];

        if ((value = $yield.call($context, item)) === $breaker) {
          return $breaker.$v;
        }

        if (value !== false && value !== nil) {
          result.push(item);
        }
      }

      return result;
    
  };

  def.$select$b = $TMP_45 = function() {var $yield = $TMP_45.$P;if ($yield) { var $context = $yield.$S, $block_given = true, block = $yield; $TMP_45.$P = null; }else { $yield = $no_proc, block = nil; }

    if ($block_given) {} else {return this.$enum_for("select!")};
      var original = this.length;

      for (var i = 0, length = original, item, value; i < length; i++) {
        item = this[i];

        if ((value = $yield.call($context, item)) === $breaker) {
          return $breaker.$v;
        }

        if (value === false || value === nil) {
          this.splice(i, 1);

          length--;
          i--;
        }
      }

      return this.length === original ? nil : this;
    
  };

  def.$shift = function(count) {

    return count === undefined ? this.shift() : this.splice(0, count);};

  $opal.alias(this, "size", "length");

  $opal.alias(this, "slice", "[]");

  def.$slice$b = function(index, length) {

    
      if (index < 0) {
        index += this.length;
      }

      if (index < 0 || index >= this.length) {
        return nil;
      }

      if (length !== undefined) {
        return this.splice(index, index + length);
      }

      return this.splice(index, 1)[0];
    };

  def.$take = function(count) {

    return this.slice(0, count);};

  def.$take_while = $TMP_46 = function() {var $yield = $TMP_46.$P;if ($yield) { var $context = $yield.$S, $block_given = true, block = $yield; $TMP_46.$P = null; }else { $yield = $no_proc, block = nil; }


    if ($block_given) {} else {return this.$enum_for("take_while")};
      var result = [];

      for (var i = 0, length = this.length, item, value; i < length; i++) {
        item = this[i];

        if ((value = $yield.call($context, item)) === $breaker) {
          return $breaker.$v;
        }

        if (value === false || value === nil) {
          return result;
        }

        result.push(item);
      }

      return result;
    
  };

  def.$to_a = function() {

    return this;};

  $opal.alias(this, "to_ary", "to_a");

  $opal.alias(this, "to_s", "inspect");

  def.$uniq = function() {

    
      var result = [],
          seen   = {};

      for (var i = 0, length = this.length, item, hash; i < length; i++) {
        item = this[i];
        hash = this.$item().$hash();

        if (!seen[hash]) {
          seen[hash] = true;

          result.push(item);
        }
      }

      return result;
    };

  def.$uniq$b = function() {

    
      var original = this.length,
          seen     = {};

      for (var i = 0, length = original, item, hash; i < length; i++) {
        item = this[i];
        hash = this.$item().$hash();

        if (!seen[hash]) {
          seen[hash] = true;
        }
        else {
          this.splice(i, 1);

          length--;
          i--;
        }
      }

      return this.length === original ? nil : this;
    };

  return def.$unshift = function(objects) {objects = $slice.call(arguments, 0);

    
      for (var i = 0, length = objects.length; i < length; i++) {
        this.unshift(objects[i]);
      }

      return this;
    };
}, 0);

$klass(this, nil, "Hash", function() {var $const = this.$const, def = this.$proto; 


  this.$include($const.Enumerable);$opal.defs(this, '$aref$', function(objs) {objs = $slice.call(arguments, 0);
    return $opal.hash.apply(null, objs);
  });

  $opal.defs(this, '$allocate', function(
    ) {return new $opal.hash();
  });

  $opal.defs(this, '$new', $TMP_47 = function(defaults) {var $yield = $TMP_47.$P;if ($yield) { var $context = $yield.$S, $block_given = true, block = $yield; $TMP_47.$P = null; }else { $yield = $no_proc, block = nil; }
    
      var hash = new $opal.hash();

      if (defaults !== undefined) {
        hash.none = defaults;
      }
      else if (block !== nil) {
        hash.proc = block;
      }

      return hash;
    
  });

  def.$eq$ = function(other) {var _a; 

    
      if (this === other) {
        return true;
      }

      if (!other.map) {
        return false;
      }

      var map  = this.map,
          map2 = other.map;

      for (var assoc in map) {
        if (!map2[assoc]) {
          return false;
        }

        var obj  = map[assoc][1],
            obj2 = map2[assoc][1];

        if (((_a = (obj).$eq$(obj2)) === false || _a === nil)) {
          return false;
        }
      }

      return true;
    };

  def.$aref$ = function(key) {

    
      var hash = key.$hash(),
          bucket;

      if (bucket = this.map[hash]) {
        return bucket[1];
      }

      return this.none;
    };

  def.$aset$ = function(key, value) {

    
      var hash       = key.$hash();
      this.map[hash] = [key, value];

      return value;
    };

  def.$assoc = function(object) {

    
      for (var assoc in this.map) {
        var bucket = this.map[assoc];

        if ((bucket[0]).$eq$(object)) {
          return [bucket[0], bucket[1]];
        }
      }

      return nil;
    };

  def.$clear = function() {

    
      this.map = {};

      return this;
    };

  def.$clone = function() {

    
      var result = new $opal.hash(),
          map    = this.map,
          map2   = result.map;

      for (var assoc in map) {
        map2[assoc] = [map[assoc][0], map[assoc][1]];
      }

      return result;
    };

  def.$default = function() {

    return this.none;};

  def.$default$e = function(object) {

    return this.none = object;};

  def.$default_proc = function() {

    return this.proc;};

  def.$default_proc$e = function(proc) {

    return this.proc = proc;};

  def.$delete = function(key) {

    
      var map  = this.map,
          hash = key.$hash(),
          result;

      if (result = map[hash]) {
        result = bucket[1];

        delete map[hash];
      }

      return result;
    };

  def.$delete_if = $TMP_48 = function() {var $yield = $TMP_48.$P;if ($yield) { var $context = $yield.$S, $block_given = true, block = $yield; $TMP_48.$P = null; }else { $yield = $no_proc, block = nil; }


    if ($block_given) {} else {return this.$enum_for("delete_if")};
      var map = this.map;

      for (var assoc in map) {
        var bucket = map[assoc],
            value;

        if ((value = $yield.call($context, bucket[0], bucket[1])) === $breaker) {
          return $breaker.$v;
        }

        if (value !== false && value !== nil) {
          delete map[assoc];
        }
      }

      return this;
    
  };

  def.$each = $TMP_49 = function() {var $yield = $TMP_49.$P;if ($yield) { var $context = $yield.$S, $block_given = true, block = $yield; $TMP_49.$P = null; }else { $yield = $no_proc, block = nil; }


    if ($block_given) {} else {return this.$enum_for("each")};
      var map = this.map;

      for (var assoc in map) {
        var bucket = map[assoc];

        if ($yield.call($context, bucket[0], bucket[1]) === $breaker) {
          return $breaker.$v;
        }
      }

      return this;
    
  };

  def.$each_key = $TMP_50 = function() {var $yield = $TMP_50.$P;if ($yield) { var $context = $yield.$S, $block_given = true, block = $yield; $TMP_50.$P = null; }else { $yield = $no_proc, block = nil; }


    if ($block_given) {} else {return this.$enum_for("each_key")};
      var map = this.map;

      for (var assoc in map) {
        var bucket = map[assoc];

        if ($yield.call($context, bucket[0]) === $breaker) {
          return $breaker.$v;
        }
      }

      return this;
    
  };

  $opal.alias(this, "each_pair", "each");

  def.$each_value = $TMP_51 = function() {var $yield = $TMP_51.$P;if ($yield) { var $context = $yield.$S, $block_given = true, block = $yield; $TMP_51.$P = null; }else { $yield = $no_proc, block = nil; }


    if ($block_given) {} else {return this.$enum_for("each_value")};
      var map = this.map;

      for (var assoc in map) {
        var bucket = map[assoc];

        if ($yield.call($context, bucket[1]) === $breaker) {
          return $breaker.$v;
        }
      }

      return this;
    
  };

  def.$empty$p = function() {

    
      for (var assoc in this.map) {
        return false;
      }

      return true;
    };

  $opal.alias(this, "eql?", "==");

  def.$fetch = $TMP_52 = function(key, defaults) {var $yield = $TMP_52.$P;if ($yield) { var $context = $yield.$S, $block_given = true, block = $yield; $TMP_52.$P = null; }else { $yield = $no_proc, block = nil; }

    
      var bucket = this.map[key.$hash()];

      if (block !== nil) {
        var value;

        if ((value = $yield.call($context, key)) === $breaker) {
          return $breaker.$v;
        }

        return value;
      }

      if (defaults !== undefined) {
        return defaults;
      }

      raise(RubyKeyError, 'key not found');
    };

  def.$flatten = function(level) {var _a, _b; 

    
      var map    = this.map,
          result = [];

      for (var assoc in map) {
        var bucket = map[assoc],
            key    = bucket[0],
            value  = bucket[1];

        result.push(key);

        if (value.$flags & T_ARRAY) {
          if (level === undefined || level === 1) {
            result.push(value);
          }
          else {
            result = result.concat((value).$flatten((_a = level, _b = 1, typeof(_a) === 'number' ? _a - _b : _a.$minus$(_b))));
          }
        }
        else {
          result.push(value);
        }
      }

      return result;
    };

  def.$has_key$p = function(key) {

    return !!this.map[key.$hash()];};

  def.$has_value$p = function(value) {

    
      for (var assoc in this.map) {
        if ((this.map[assoc][1]).$eq$(value)) {
          return true;
        }
      }

      return false;
    };

  def.$hash = function() {

    return this.$id;};

  def.$inspect = function() {

    
      var inspect = [],
          map     = this.map;

      for (var assoc in map) {
        var bucket = map[assoc];

        inspect.push((bucket[0]).$inspect() + '=>' + (bucket[1]).$inspect());
      }
      return '{' + inspect.join(', ') + '}';
    };

  def.$invert = function() {

    
      var result = $opal.hash(),
          map    = this.map,
          map2   = result.map;

      for (var assoc in map) {
        var bucket = map[assoc];

        map2[(bucket[1]).$hash()] = [bucket[0], bucket[1]];
      }

      return result;
    };

  def.$key = function(object) {

    
      for (var assoc in this.map) {
        var bucket = this.map[assoc];

        if (object.$eq$(bucket[1])) {
          return bucket[0];
        }
      }

      return nil;
    };

  $opal.alias(this, "key?", "has_key?");

  def.$keys = function() {

    
      var result = [];

      for (var assoc in this.map) {
        result.push(this.map[assoc][0]);
      }

      return result;
    };

  def.$length = function() {

    
      var result = 0;

      for (var assoc in this.map) {
        result++;
      }

      return result;
    };

  $opal.alias(this, "member?", "has_key?");

  def.$merge = function(other) {

    
      var result = $opal.hash(),
          map    = this.map,
          map2   = result.map;

      for (var assoc in map) {
        var bucket = map[assoc];

        map2[assoc] = [bucket[0], bucket[1]];
      }

      map = other.map;

      for (var assoc in map) {
        var bucket = map[assoc];

        map2[assoc] = [bucket[0], bucket[1]];
      }

      return result;
    };

  def.$merge$b = function(other) {

    
      var map  = this.map,
          map2 = other.map;

      for (var assoc in map2) {
        var bucket = map2[assoc];

        map[assoc] = [bucket[0], bucket[1]];
      }

      return this;
    };

  def.$rassoc = function(object) {

    
      var map = this.map;

      for (var assoc in map) {
        var bucket = map[assoc];

        if ((bucket[1]).$eq$(object)) {
          return [bucket[0], bucket[1]];
        }
      }

      return nil;
    };

  def.$replace = function(other) {

    
      var map = this.map = {};

      for (var assoc in other.map) {
        var bucket = other.map[assoc];

        map[assoc] = [bucket[0], bucket[1]];
      }

      return this;
    };

  $opal.alias(this, "size", "length");

  def.$to_a = function() {

    
      var map    = this.map,
          result = [];

      for (var assoc in map) {
        var bucket = map[assoc];

        result.push([bucket[0], bucket[1]]);
      }

      return result;
    };

  def.$to_hash = function() {

    return this;};

  $opal.alias(this, "to_s", "inspect");

  $opal.alias(this, "update", "merge!");

  return def.$values = function() {

    
      var map    = this.map,
          result = [];

      for (var assoc in map) {
        result.push(map[assoc][1]);
      }

      return result;
    };
}, 0);

$klass(this, nil, "String", function() {var $const = this.$const, def = this.$proto; 
  $opal.defs(this, '$new', function(str) {if (str === undefined) { str = ""; }
    return str.$to_s()
  });

  def.$lt$ = function(other) {

    return this < other;};

  def.$le$ = function(other) {

    return this <= other;};

  def.$gt$ = function(other) {

    return this > other;};

  def.$ge$ = function(other) {

    return this >= other;};

  def.$plus$ = function(other) {

    return this + other;};

  def.$aref$ = function(index, length) {

    return this.substr(index, length);};

  def.$eq$ = function(other) {

    return this.valueOf() === other.valueOf();};

  def.$match$ = function(other) {

    
      if (typeof other === 'string') {
        raise(RubyTypeError, 'string given');
      }

      return other.$match$(this);
    };

  def.$cmp$ = function(other) {

    
      if (typeof other !== 'string') {
        return nil;
      }

      return this > other ? 1 : (this < other ? -1 : 0);
    };

  def.$capitalize = function() {

    return this.charAt(0).toUpperCase() + this.substr(1).toLowerCase();};

  def.$casecmp = function(other) {

    
      if (typeof other !== 'string') {
        return other;
      }

      var a = this.toLowerCase(),
          b = other.toLowerCase();

      return a > b ? 1 : (a < b ? -1 : 0);
    };

  def.$downcase = function() {

    return this.toLowerCase();};

  def.$end_with$p = function(suffix) {

    return this.lastIndexOf(suffix) === this.length - suffix.length;};

  def.$empty$p = function() {

    return this.length === 0;};

  def.$gsub = $TMP_53 = function(pattern, replace) {var _a, _b, _c; var $yield = $TMP_53.$P;if ($yield) { var $context = $yield.$S, $block_given = true, block = $yield; $TMP_53.$P = null; }else { $yield = $no_proc, block = nil; }

    
      var re = pattern.toString();
          re = re.substr(1, re.lastIndexOf('/') - 1);
          re = new RegExp(re, 'g');

      return (_a=(_b=this).$sub, _a.$P = (_c = block, (typeof(_c) === 'function' || _c == nil ? _c : _c.$to_proc())), _a).call(_b, this.$re(), replace);
    };

  def.$hash = function() {

    return this.toString();};

  def.$include$p = function(other) {

    return this.indexOf(other) !== -1;};

  def.$index = function(substr) {

    
      var result = this.indexOf(substr);
      return result === -1 ? nil : result
    };

  def.$inspect = function() {

    
      var escapable = /[\\\"\x00-\x1f\x7f-\x9f\u00ad\u0600-\u0604\u070f\u17b4\u17b5\u200c-\u200f\u2028-\u202f\u2060-\u206f\ufeff\ufff0-\uffff]/g,
          meta      = {
            '\b': '\\b',
            '\t': '\\t',
            '\n': '\\n',
            '\f': '\\f',
            '\r': '\\r',
            '"' : '\\"',
            '\\': '\\\\'
          };

      escapable.lastIndex = 0;

      return escapable.test(this) ? '"' + this.replace(escapable, function(a) {
        var c = meta[a];

        return typeof c === 'string' ? c :
          '\\u' + ('0000' + a.charCodeAt(0).toString(16)).slice(-4);
      }) + '"' : '"' + this + '"';
  };

  def.$intern = function() {

    return this;};

  def.$length = function() {

    return this.length;};

  def.$lstrip = function() {

    return this.replace(/^s*/, '');};

  def.$next = function() {

    return String.fromCharCode(this.charCodeAt(0));};

  def.$reverse = function() {

    return this.split('').reverse().join('');};

  def.$split = function(split, limit) {

    return this.split(split, limit);};

  def.$start_with$p = function(prefix) {

    return this.indexOf(prefix) === 0;};

  def.$sub = $TMP_54 = function(pattern, replace) {var $yield = $TMP_54.$P;if ($yield) { var $context = $yield.$S, $block_given = true, block = $yield; $TMP_54.$P = null; }else { $yield = $no_proc, block = nil; }

    
      if (block !== nil) {
        return this.replace(pattern, function(str) {
          return $yield.call($context, str);
        });
      }
      else {
        return this.replace(pattern, replace);
      }
    };

  $opal.alias(this, "succ", "next");

  def.$to_f = function() {

    return parseFloat(this);};

  def.$to_i = function(base) {if (base === undefined) { base = 10; }

    return parseInt(this, base);};

  def.$to_proc = function() {

    
      var self = this;
      return function(iter, arg) { return arg['$' + self](); };
    };

  def.$to_s = function() {

    return this.toString();};

  $opal.alias(this, "to_sym", "intern");

  return def.$upcase = function() {

    return this.toUpperCase();};
}, 0);

$const.Symbol = 

$const.String;$klass(this, nil, "Numeric", function() {var $const = this.$const, def = this.$proto; 
  def.$plus$ = function(other) {

    return this + other;};

  def.$minus$ = function(other) {

    return this - other;};

  def.$mul$ = function(other) {

    return this * other;};

  def.$div$ = function(other) {

    return this / other;};

  def.$mod$ = function(other) {

    return this % other;};

  def.$and$ = function(other) {

    return this & other;};

  def.$or$ = function(other) {

    return this | other;};

  def.$xor$ = function(other) {

    return this ^ other;};

  def.$lt$ = function(other) {

    return this < other;};

  def.$le$ = function(other) {

    return this <= other;};

  def.$gt$ = function(other) {

    return this > other;};

  def.$ge$ = function(other) {

    return this >= other;};

  def.$lshft$ = function(count) {

    return this << count;};

  def.$rshft$ = function(count) {

    return this >> count;};

  def.$uplus$ = function() {

    return +this;};

  def.$uminus$ = function() {

    return -this;};

  def.$tild$ = function() {

    return ~this;};

  def.$pow$ = function(other) {

    return Math.pow(this, other);};

  def.$eq$ = function(other) {

    return this.valueOf() === other.valueOf();};

  def.$cmp$ = function(other) {

    
      if (typeof(other) !== 'number') {
        return nil;
      }

      return this < other ? -1 : (this > other ? 1 : 0);
    };

  def.$abs = function() {

    return Math.abs(this);};

  def.$ceil = function() {

    return Math.ceil(this);};

  def.$downto = $TMP_55 = function(finish) {var $yield = $TMP_55.$P;if ($yield) { var $context = $yield.$S, $block_given = true, block = $yield; $TMP_55.$P = null; }else { $yield = $no_proc, block = nil; }


    if ($block_given) {} else {return this.$enum_for("downto", finish)};
      for (var i = this; i >= finish; i--) {
        if ($yield.call($context, i) === $breaker) {
          return $breaker.$v;
        }
      }

      return this;
    
  };

  def.$even$p = function() {

    return this % 2 === 0;};

  def.$floor = function() {

    return Math.floor(this);};

  def.$hash = function() {

    return this.toString();};

  def.$integer$p = function() {

    return this % 1 === 0;};

  $opal.alias(this, "magnitude", "abs");

  $opal.alias(this, "modulo", "%");

  def.$next = function() {

    return this + 1;};

  def.$nonzero$p = function() {

    return this.valueOf() === 0 ? nil : this;};

  def.$odd$p = function() {

    return this % 2 !== 0;};

  def.$pred = function() {

    return this - 1;};

  $opal.alias(this, "succ", "next");

  def.$times = $TMP_56 = function() {var _a; var $yield = $TMP_56.$P;if ($yield) { var $context = $yield.$S, $block_given = true, block = $yield; $TMP_56.$P = null; }else { $yield = $no_proc, block = nil; }


    if ((_a = block) !== false && _a !== nil) {} else {return this.$enum_for("times")};
      for (var i = 0; i <= this; i++) {
        if ($yield.call($context, i) === $breaker) {
          return $breaker.$v;
        }
      }

      return this;
    
  };

  def.$to_f = function() {

    return parseFloat(this);};

  def.$to_i = function() {

    return parseInt(this);};

  def.$to_s = function(base) {if (base === undefined) { base = 10; }

    return this.toString(base);};

  def.$upto = $TMP_57 = function(finish) {var $yield = $TMP_57.$P;if ($yield) { var $context = $yield.$S, $block_given = true, block = $yield; $TMP_57.$P = null; }else { $yield = $no_proc, block = nil; }


    if ($block_given) {} else {return this.$enum_for("upto", finish)};
      for (var i = 0; i <= finish; i++) {
        if ($yield.call($context, i) === $breaker) {
          return $breaker.$v;
        }
      }

      return this;
    
  };

  return def.$zero$p = function() {

    return this.valueOf() === 0;};
}, 0);

$klass(this, nil, "Integer", function() {var $const = this.$const, def = this.$proto; 
  return $opal.defs(this, '$eqq$', function(obj) {
    
      if (typeof(obj) !== 'number') {
        return false;
      }

      return other % 1 === 0;
    
  })
}, 0);

$klass(this, nil, "Float", function() {var $const = this.$const, def = this.$proto; 
  return $opal.defs(this, '$eqq$', function(obj) {
    
      if (typeof(obj) !== 'number') {
        return false;
      }

      return obj % 1 !== 0;
    
  })
}, 0);

$klass(this, nil, "Proc", function() {var $const = this.$const, def = this.$proto; 
  $opal.defs(this, '$new', $TMP_58 = function() {var $yield = $TMP_58.$P;if ($yield) { var $context = $yield.$S, $block_given = true, block = $yield; $TMP_58.$P = null; }else { $yield = $no_proc, block = nil; }


    if ($block_given) {} else {this.$raise($const.ArgumentError, "tried to create Proc object without a block")};
    return block;});

  def.$to_proc = function() {

    return this;};

  def.$call = function(args) {args = $slice.call(arguments, 0);

    return this.apply(this.$S, args);};

  def.$to_proc = function() {

    return this;};

  def.$to_s = function() {

    return "#<Proc:0x0000000>";};

  def.$lambda$p = function() {

    return !!this.$lambda;};

  return def.$arity = function() {

    return this.length - 1;};
}, 0);

$klass(this, nil, "Range", function() {var $const = this.$const, def = this.$proto; 
  def.$begin = function() {

    return this.begin;};

  def.$end = function() {

    return this.end;};

  $opal.alias(this, "first", "begin");
  $opal.alias(this, "min", "begin");

  $opal.alias(this, "last", "end");
  $opal.alias(this, "max", "end");

  def.$initialize = function(min, max, exclude) {if (exclude === undefined) { exclude = false; }
    this.begin = 
    min;this.end = 
    max;return this.exclude = 
    exclude;};


  def.$eqq$ = function(obj) {

    return obj >= this.begin && obj <= this.end;};

  def.$exclude_end$p = function() {

    return this.exclude;};

  def.$to_s = function() {

    return this.begin + (this.exclude ? '...' : '..') + this.end;};

  return def.$inspect = function() {

    return this.begin + (this.exclude ? '...' : '..') + this.end;};
}, 0);

$klass(this, nil, "Exception", function() {var $const = this.$const, def = this.$proto; 
  def.$initialize = function(message) {if (message === undefined) { message = ""; }

    
      if (Error.captureStackTrace) {
        Error.captureStackTrace(this);
      }

      this.message = message;
    };

  def.$backtrace = function() {

    
      if (this._bt !== undefined) {
        return this._bt;
      }

      var backtrace = this.stack;

      if (typeof(backtrace) === 'string') {
        return this._bt = backtrace.split("\n");
      }
      else if (backtrace) {
        this._bt = backtrace;
      }

      return this._bt = ["No backtrace available"];
    };

  def.$inspect = function() {

    return ("#<" + this.$class().$to_s() + ": '" + this.$message().$to_s() + "'>");};

  def.$message = function() {

    return this.message;};

  return $opal.alias(this, "to_s", "message");
}, 0);

$klass(this, nil, "Regexp", function() {var $const = this.$const, def = this.$proto; 
  $opal.defs(this, '$escape', function(string) {
    return string.replace(/([.*+?^=!:${}()|[]\/\])/g, '\$1');
  });

  $opal.defs(this, '$new', function(string, options) {
    return new RegExp(string, options);
  });

  def.$eq$ = function(other) {

    return other.constructor == RegExp && this.toString() === other.toString();};

  def.$eqq$ = function(obj) {

    return this.test(obj);};

  def.$match$ = function(string) {

    
      var result = this.exec(string);

      if (result) {
        var match = new RubyMatch.$allocator();
        match.$data = result;
        ($opal.gvars["$~"] = match);
      }
      else {
        ($opal.gvars["$~"] = nil);
      }

      return result ? result.index : nil;
    };

  $opal.alias(this, "eql?", "==");

  def.$inspect = function() {

    return this.toString();};

  def.$match = function(pattern) {

    
      var result  = this.exec(pattern);

      if (result) {
        var match   = new RubyMatch.$allocator();
        match.$data = result;
        return ($opal.gvars["$~"] = match);
      }
      else {
        return ($opal.gvars["$~"] = nil);
      }
    };

  return def.$to_s = function() {

    return this.source;};
}, 0);

$klass(this, nil, "MatchData", function() {var $const = this.$const, def = this.$proto; 
  def.$aref$ = function(index) {

    
      var length = this.$data.length;

      if (index < 0) {
        index += length;
      }

      if (index >= length || index < 0) {
        return nil;
      }

      return this.$data[index];
    };

  def.$length = function() {

    return this.$data.length;};

  def.$inspect = function() {

    return ("#<MatchData " + this.$aref$(0).$inspect().$to_s() + ">");};

  $opal.alias(this, "size", "length");

  def.$to_a = function() {

    return $slice.call(this.$data);};

  return def.$to_s = function() {

    return this.$data[0];};
}, 0);

$klass(this, nil, "Time", function() {var $const = this.$const, def = this.$proto; 


  this.$include($const.Comparable);$opal.defs(this, '$at', function(seconds, frac) {var result = nil; if (frac === undefined) { frac = 0; }
    result = 
    this.$allocate();result.time = new Date(seconds * 1000 + frac);

    return result;});

  $opal.defs(this, '$now', function(
    ) {var result = nil; result = 
    this.$allocate();result.time = new Date();

    return result;});

  def.$initialize = function() {

    return this.time = new Date();};

  def.$plus$ = function(other) {var _a, _b; 

    
      var res = $const.Time.$allocate();
      res.time = new Date((_a = this.$to_f(), _b = other.$to_f(), typeof(_a) === 'number' ? _a + _b : _a.$plus$(_b)));
      return res;
    };

  def.$minus$ = function(other) {var _a, _b; 

    
      var res = $const.Time.$allocate();
      res.time = new Date((_a = this.$to_f(), _b = other.$to_f(), typeof(_a) === 'number' ? _a - _b : _a.$minus$(_b)));
      return res;
    };

  def.$cmp$ = function(other) {

    return this.$to_f().$cmp$(other.$to_f());};

  def.$day = function() {

    return this.time.getDate();};

  def.$eql$p = function(other) {var _a; 

    return (_a = other.$is_a$p($const.Time), _a !== false && _a != nil ? this.$cmp$(other).$zero$p() : _a);};

  def.$friday$p = function() {

    return this.time.getDay() === 5;};

  def.$hour = function() {

    return this.time.getHours();};

  $opal.alias(this, "mday", "day");

  def.$min = function() {

    return this.time.getMinutes();};

  def.$mon = function() {

    return this.time.getMonth() + 1;};

  def.$monday$p = function() {

    return this.time.getDay() === 1;};

  $opal.alias(this, "month", "mon");

  def.$saturday$p = function() {

    return this.time.getDay() === 6;};

  def.$sec = function() {

    return this.time.getSeconds();};

  def.$sunday$p = function() {

    return this.time.getDay() === 0;};

  def.$thursday$p = function() {

    return this.time.getDay() === 4;};

  def.$to_f = function() {

    return this.time.getTime() / 1000;};

  def.$to_i = function() {

    return parseInt(this.time.getTime() / 1000);};

  def.$tuesday$p = function() {

    return this.time.getDay() === 2;};

  def.$wday = function() {

    return this.time.getDay();};

  def.$wednesday$p = function() {

    return this.time.getDay() === 3;};

  return def.$year = function() {

    return this.time.getFullYear();};
}, 0);

$klass(this, nil, "Struct", function() {var $const = this.$const, def = this.$proto; 
  $opal.defs(this, '$new', function(name, args) {var _a, _b; args = $slice.call(arguments, 1);
    if ((_a = this.$eq$(

    $const.Struct)) !== false && _a !== nil) {} else {return $opal.zuper(arguments.callee, this, [])};if ((_a = name.$is_a$p($const.String)) !== false && _a !== nil) {
      return $const.Struct.$const_set(name, (_a=this).$new.apply(_a, args))} else {

      args.$unshift(

      name);return (_a=(_b=$const.Class).$new, (_a.$P = function() {var _a, _b; 
        return (_a=(_b=args).$each, (_a.$P = function(name) {if (name === undefined) {name = nil; }return this.$define_struct_attribute(name)}).$S = this, _a).call(_b)
      }).$S = this, _a).call(_b, this);
    };
  });

  $opal.defs(this, '$define_struct_attribute', function(name) {var _a, _b; 
    this.$members().$lshft$(

    name);(_a=(_b=this).$define_method, (_a.$P = function() {
      return this.$instance_variable_get(("@" + name.$to_s()))
    }).$S = this, _a).call(_b, name);

    return (_a=(_b=this).$define_method, (_a.$P = function(value) {if (value === undefined) {value = nil; }
      return this.$instance_variable_set(("@" + name.$to_s()), 
      value)}).$S = this, _a).call(_b, ("" + name.$to_s() + "="));
  });

  $opal.defs(this, '$members', function(
    ) {var _a; this.members == null && (this.members = nil);return (_a = this.members, _a !== false && _a != nil ? _a : this.members = [])
  });



  this.$include($const.Enumerable);def.$initialize = function(args) {var _a, _b; args = $slice.call(arguments, 0);



    return (_a=(_b=this.$members()).$each_with_index, (_a.$P = function(name, index) {if (name === undefined) {name = nil; }if (index === undefined) {index = nil; }return this.$instance_variable_set(("@" + name.$to_s()), args.$aref$(index))}).$S = this, _a).call(_b);};

  def.$members = function() {

    return this.$class().$members();};

  def.$aref$ = function(name) {var _a, _b; 
    if ((_a = name.$is_a$p($const.Integer)) !== false && _a !== nil) {
      if ((_a = name, _b = this.$members().$size(), typeof(_a) === 'number' ? _a >= _b : _a.$ge$(_b))) {this.$raise($const.IndexError, ("offset " + name.$to_s() + " too large for struct(size:" + this.$members().$size().$to_s() + ")"))

      };name = this.$members().$aref$(name);} else {

      if ((_b = this.$members().$include$p(name.$to_sym())) !== false && _b !== nil) {} else {this.$raise($const.NameError, ("no member '" + name.$to_s() + "' in struct"))
      }};

    return this.$instance_variable_get(("@" + name.$to_s()));
  };

  def.$aset$ = function(name, value) {var _a, _b; 
    if ((_a = name.$is_a$p($const.Integer)) !== false && _a !== nil) {
      if ((_a = name, _b = this.$members().$size(), typeof(_a) === 'number' ? _a >= _b : _a.$ge$(_b))) {this.$raise($const.IndexError, ("offset " + name.$to_s() + " too large for struct(size:" + this.$members().$size().$to_s() + ")"))

      };name = this.$members().$aref$(name);} else {

      if ((_b = this.$members().$include$p(name.$to_sym())) !== false && _b !== nil) {} else {this.$raise($const.NameError, ("no member '" + name.$to_s() + "' in struct"))
      }};

    return this.$instance_variable_set(("@" + name.$to_s()), 
    value);};

  def.$each = $TMP_59 = function() {var _a, _b; try {var $yield = $TMP_59.$P;if ($yield) { var $context = $yield.$S, $block_given = true; $TMP_59.$P = null; }else { $yield = $no_proc; }


    if ($block_given) {} else {return this.$enum_for("each")};return (_a=(_b=this.$members()).$each, (_a.$P = function(name) {var _a; if (name === undefined) {name = nil; }return ((_a = $yield.call($context, this.$aref$(name))) === $breaker ? _a.$t() : _a)}).$S = this, _a).call(_b);} catch (e) { if (e === $breaker) { return e.$v; }; throw e;}
  };

  def.$each_pair = $TMP_60 = function() {var _a, _b; try {var $yield = $TMP_60.$P;if ($yield) { var $context = $yield.$S, $block_given = true; $TMP_60.$P = null; }else { $yield = $no_proc; }


    if ($block_given) {} else {return this.$enum_for("each_pair")};return (_a=(_b=this.$members()).$each, (_a.$P = function(name) {var _a; if (name === undefined) {name = nil; }return ((_a = $yield.call($context, name, this.$aref$(name))) === $breaker ? _a.$t() : _a)}).$S = this, _a).call(_b);} catch (e) { if (e === $breaker) { return e.$v; }; throw e;}
  };

  def.$eql$p = function(other) {var _a, _b, _c; 



    return (_a = this.$hash().$eq$(other.$hash()), _a !== false && _a != nil ? _a : (_b=(_c=other.$each_with_index()).$all$p, (_b.$P = function(object, index) {if (object === undefined) {object = nil; }if (index === undefined) {index = nil; }return this.$aref$(this.$members().$aref$(index)).$eq$(object)}).$S = this, _b).call(_c));};

  def.$length = function() {

    return this.$members().$length();};

  $opal.alias(this, "size", "length");

  def.$to_a = function() {var _a, _b; 

    return (_a=(_b=this.$members()).$map, (_a.$P = function(name) {if (name === undefined) {name = nil; }return this.$aref$(name)}).$S = this, _a).call(_b);};

  return $opal.alias(this, "values", "to_a");
}, 0);

$klass(this, nil, "IO", function() {var $const = this.$const, def = this.$proto; 
  def.$puts = function(args) {var _a, _b; args = $slice.call(arguments, 0);
    if ((_a = args.$empty$p()) !== false && _a !== nil) {return this.$flush()

    };return (_a=(_b=args).$each, (_a.$P = function(a) {if (a === undefined) {a = nil; }
      this.$write(a.$to_s());

      return this.$flush();}).$S = this, _a).call(_b);
  };

  def.$print = function(args) {var _a, _b; args = $slice.call(arguments, 0);
    (_a=(_b=args).$each, (_a.$P = function(a) {if (a === undefined) {a = nil; }return this.$write(a.$to_s())}).$S = this, _a).call(_b);

    return nil;
  };

  def.$write = function() {

    return nil;};

  return def.$flush = function() {

    return this;};
}, 0);

$const.STDOUT = ($opal.gvars["$stdout"] = $const.IO.$new());

$klass(((_a = $opal.gvars["$stdout"]) == null ? nil : _a), nil, nil, function() {var $const = this.$const; 

var stdout_buffer = [];

$opal.defn(this, '$write', function(str) {
  stdout_buffer.push(str);

  return nil;
});

return $opal.defn(this, '$flush', function() {
  console.log(stdout_buffer.join(''));
  stdout_buffer = [];

  return nil;
});}, 2);


$klass(this, nil, "File", function() {var $const = this.$const, def = this.$proto; 

  $const.PATH_RE = /^(.+\/(?!$)|\/)?((?:.+?)?(\.[^.]*)?)$/;

  $opal.defs(this, '$expand_path', function(path, base) {
    
      if (!base) {
        if (path.charAt(0) !== '/') {
          base = FS_CWD;
        }
        else {
          base = '';
        }
      }

      path = this.$join(base, path);

      var parts = path.split('/'), result = [], path;

      // initial '/'
      if (parts[0] === '') {
        result.push('');
      }

      for (var i = 0, ii = parts.length; i < ii; i++) {
        part = parts[i];

        if (part === '..') {
          result.pop();
        }
        else if (part === '.' || part === '') {

        }
        else {
          result.push(part);
        }
      }

      return result.join('/');
    
  });

  $opal.defs(this, '$join', function(paths) {paths = $slice.call(arguments, 0);
    return paths.join('/');
  });

  $opal.defs(this, '$dirname', function(path) {
    
      var dirname = $const.PATH_RE.exec(path)[1];

      if (!dirname) {
        return '.';
      }
      else if (dirname === '/') {
        return dirname;
      }
      else {
        return dirname.substring(0, dirname.length - 1);
      }
    
  });

  $opal.defs(this, '$extname', function(path) {
    
      var extname = $const.PATH_RE.exec(path)[3];

      if (!extname || extname === '.') {
        return '';
      }
      else {
        return extname;
      }
    
  });

  $opal.defs(this, '$basename', function(path, suffix) {
    return $opal.fs.basename(path, suffix);
  });

  return $opal.defs(this, '$exist$p', function(path) {
    return !!FACTORIES[this.$expand_path(path)];
  });
}, 0);

return $klass(this, nil, "Dir", function() {var $const = this.$const, def = this.$proto; 
  $opal.defs(this, '$getwd', function(
    ) {return FS_CWD;
  });

  $opal.defs(this, '$pwd', function(
    ) {return FS_CWD;
  });

  return $opal.defs(this, '$aref$', function(globs) {globs = $slice.call(arguments, 0);
    
      var result = [], files = FACTORIES;

      for (var i = 0, ii = globs.length; i < ii; i++) {
        var glob = globs[i];

        var re = fs_glob_to_regexp($const.File.$expand_path(glob));

        for (var file in files) {
          if (re.exec(file)) {
            result.push(file);
          }
        }
      }

      return result;
    
  });
}, 0);;var $TMP_1, $TMP_2, $TMP_3, $TMP_4, $TMP_5, $TMP_6, $TMP_7, $TMP_8, $TMP_9, $TMP_10, $TMP_11, $TMP_12, $TMP_13, $TMP_14, $TMP_15, $TMP_16, $TMP_17, $TMP_18, $TMP_19, $TMP_20, $TMP_21, $TMP_22, $TMP_23, $TMP_24, $TMP_25, $TMP_26, $TMP_27, $TMP_28, $TMP_29, $TMP_30, $TMP_31, $TMP_32, $TMP_33, $TMP_34, $TMP_35, $TMP_36, $TMP_37, $TMP_38, $TMP_39, $TMP_40, $TMP_41, $TMP_42, $TMP_43, $TMP_44, $TMP_45, $TMP_46, $TMP_47, $TMP_48, $TMP_49, $TMP_50, $TMP_51, $TMP_52, $TMP_53, $TMP_54, $TMP_55, $TMP_56, $TMP_57, $TMP_58, $TMP_59, $TMP_60;
}).call(opal.top, opal);
}).call(this);