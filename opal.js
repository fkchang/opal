/*!
 * opal v0.3.15
 * http://adambeynon.github.com/opal
 *
 * Copyright 2012, Adam Beynon
 * Released under the MIT license
 */
(function(undefined) {
var opal = this.opal = {};

// Minify common function calls
var ArrayProto          = Array.prototype,
    ObjectProto         = Object.prototype,
    $slice              = ArrayProto.slice,
    hasOwnProperty      = ObjectProto.hasOwnProperty;

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

function define_attr_bridge(klass, target, name, getter, setter) {
  if (getter) {
    define_method(klass, mid_to_jsid(name), function() {
      var res = target[name];

      return res == null ? nil : res;
    });
  }

  if (setter) {
    define_method(klass, mid_to_jsid(name + '='), function (block, val) {
      return target[name] = val;
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
    assocs[key.m$hash()] = [key, args[++i]];
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

// Set constant with given id
opal.const_set = function(base, id, val) {
  if (base.$flags & T_OBJECT) {
    base = class_real(base.$klass);
  }

  return base.$const[id] = val;
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
    raise(RubyNameError, "undefined method `" + old_name + "' for class `" + klass.__classid__ + "'");
  }

  define_method(klass, new_name, body);
  return nil;
};

// method missing yielder - used in debug mode to call method_missing.
opal.mm = function(jsid) {
  var mid = jsid_to_mid(jsid);
  return function(block) {
    var args = $slice.call(arguments, 1);
    args.unshift(mid);
    args.unshift(block);
    return this.m$method_missing.apply(this, args);
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
  klass.$m[id]           = body;

  var included_in = klass.$included_in, includee;

  if (included_in) {
    for (var i = 0, ii = included_in.length; i < ii; i++) {
      includee = included_in[i];

      define_method(includee, id, body);
    }
  }

  // Add method to toll-free prototypes as well
  if (klass.$bridge_prototype) {
    klass.$bridge_prototype[id] = body;
  }


  return nil;
}

function define_method_bridge(klass, target, id, name) {
  define_method(klass, id, function() {
    return target.apply(this, $slice.call(arguments, 1));
  });
}

function string_inspect(self) {
  /* borrowed from json2.js, see file for license */
  var cx        = /[\u0000\u00ad\u0600-\u0604\u070f\u17b4\u17b5\u200c-\u200f\u2028-\u202f\u2060-\u206f\ufeff\ufff0-\uffff]/g,
      escapable = /[\\\"\x00-\x1f\x7f-\x9f\u00ad\u0600-\u0604\u070f\u17b4\u17b5\u200c-\u200f\u2028-\u202f\u2060-\u206f\ufeff\ufff0-\uffff]/g,
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

  return escapable.test(self) ? '"' + self.replace(escapable, function(a) {
    var c = meta[a];

    return typeof c === 'string' ? c :
      '\\u' + ('0000' + a.charCodeAt(0).toString(16)).slice(-4);
  }) + '"' : '"' + self + '"';
};

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
  module.__classid__ = (base === RubyObject ? id : base.__classid__ + '::' + id)

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

      if (base.$const.hasOwnProperty(id)) {
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

      if (base.$const.hasOwnProperty(id)) {
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
             + " for " + self.$m.inspect(self, 'inspect'));
  }

  args.unshift(null);
  return func.apply(self, args);
};

function mid_to_jsid(mid) {
  if (method_names[mid]) {
    return method_names[mid];
  }

  return 'm$' + mid.replace('!', '$b').replace('?', '$p').replace('=', '$e');
}

function jsid_to_mid(jsid) {
  if (reverse_method_names[jsid]) {
    return reverse_method_names[jsid];
  }

  jsid = jsid.substr(2); // remove 'm$'

  return jsid.replace('$b', '!').replace('$p', '?').replace('$e', '=');
}

// Raise a new exception using exception class and message
function raise(exc, str) {
  throw exc.m$new(null, str);
}

opal.arg_error = function(given, expected) {
  raise(RubyArgError, 'wrong number of arguments(' + given + ' for ' + expected + ')');
};

// Inspect object or class
function inspect_object(obj) {
  if (obj.$flags & T_OBJECT) {
    return "#<" + class_real(obj.$klass).__classid__ + ":0x" + (obj.$id * 400487).toString(16) + ">";
  }
  else {
    return obj.__classid__;
  }
}
// Root of all objects and classes inside opal
function RootObject() {};

RootObject.prototype.toString = function() {
  if (this.$flags & T_OBJECT) {
    return "#<" + (this.$klass).__classid__ + ":0x" + this.$id + ">";
  }
  else {
    return '<' + this.__classid__ + ' ' + this.$id + '>';
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
      proto.$m           = {};
      proto.$methods     = [];
      proto.$allocator   = klass;
      proto.$flags       = T_CLASS;
      proto.__classid__  = id;
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
  proto.$m                         = {};
  proto.$methods                   = [];
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
      var class_id = "#<Class:" + klass.__classid__ + ">",
          meta     = boot_class(superklass);

      meta.__classid__ = class_id;
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
      class_id   = "#<Class:#<" + orig_class.__classid__ + ":" + orig_class.$id + ">>";

  klass             = boot_class(orig_class);
  klass.__classid__ = class_id;

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

  var class_id = (base === RubyObject ? id : base.__classid__ + '::' + id);

  klass             = boot_class(superklass);
  klass.__classid__ = class_id;

  make_metaclass(klass, superklass.$klass);

  var const_alloc   = function() {};
  var const_scope   = const_alloc.prototype = new base.$const.alloc();
  klass.$const      = const_scope;
  const_scope.alloc = const_alloc;

  base.$const[id] = klass;

  if (superklass.m$inherited) {
    superklass.m$inherited(null, klass);
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
    var class_id = obj.$klass.__classid__;

    klass = make_metaclass(obj, obj.$klass);
  }

  return klass;
}
opal.main = function(id) {
  opal.gvars.$0 = find_lib(id);

  try {
    top_self.m$require(null, id);

    opal.do_at_exit();
  }
  catch (e) {
    // this is defined in debug.js
    if (opal.backtrace) {
      opal.backtrace(e);
    }
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

FACTORIES = {};
LIBS      = {};
LOADER_PATHS     = ['', '/lib'];
LOADER_CACHE     = {};

function find_lib(id) {
  var lib  = '/lib/' + id;

  // try to load a lib path first - i.e. something in our load path
  if (FACTORIES[lib + '.rb']) {
    return lib + '.rb';
  }

  // next, incase our require() has a ruby extension..
  if (FACTORIES[lib]) {
    return lib;
  }

  // check if id is full path..
  if (FACTORIES[id]) {
    return id;
  }

  // full path without '.rb'
  if (FACTORIES[id + '.rb']) {
    return id + '.rb';
  }

  // check in current working directory.
  var in_cwd = FS_CWD + '/' + id;

  if (FACTORIES[in_cwd]) {
    return in_cwd;
  }
};

// Split to dirname, basename and extname
var PATH_RE = /^(.+\/(?!$)|\/)?((?:.+?)?(\.[^.]*)?)$/;

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
function exc_backtrace(err) {
  var old = Error.prepareStackTrace;
  Error.prepareStackTrace = prepare_backtrace;

  var backtrace = err.stack;
  Error.prepareStackTrace = old;

  if (backtrace && backtrace.join) {
    return backtrace;
  }

  return ["No backtrace available"];
}

function prepare_backtrace(error, stack) {
  var code = [], f, b, k, name, self;

  for (var i = 0; i < stack.length; i++) {
    f = stack[i];
    b = f.getFunction();
    name = f.getMethodName();
    self = f.getThis();
    
    if (!self.$klass || !name) {
      continue;
    }
    
    self  = (self.$flags & T_OBJECT ?
           class_real(self.$klass).__classid__ + '#' :
           self.__classid__ + '.');

    code.push("from " + self + jsid_to_mid(name) + ' at ' + f.getFileName() + ":" + f.getLineNumber());
  }

  return code;
}

// Print error backtrace to console
opal.backtrace = opal.bt = function(err) {
  console.log(err.$klass.__classid__ + ": " + err.message);
  console.log("\t" + exc_backtrace(err).join("\n\t"));
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

var RubyArray     = bridge_class(Array, T_OBJECT | T_ARRAY, 'Array');
var RubyNumeric   = bridge_class(Number, T_OBJECT | T_NUMBER, 'Numeric');

var RubyHash      = bridge_class(Hash, T_OBJECT, 'Hash');

var RubyString    = bridge_class(String, T_OBJECT | T_STRING, 'String');
var RubyBoolean   = bridge_class(Boolean, T_OBJECT | T_BOOLEAN, 'Boolean');
var RubyProc      = bridge_class(Function, T_OBJECT | T_PROC, 'Proc');
var RubyRegexp    = bridge_class(RegExp, T_OBJECT, 'Regexp');

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
  return this.$klass.__classid__ + ': ' + this.message;
};

var breaker = opal.breaker  = new Error('unexpected break');
    breaker.$klass              = RubyLocalJumpError;
    breaker.$t              = function() { throw this; };

var method_names = {'==': 'm$eq$', '===': 'm$eqq$', '[]': 'm$aref$', '[]=': 'm$aset$', '~': 'm$tild$', '<=>': 'm$cmp$', '=~': 'm$match$', '+': 'm$plus$', '-': 'm$minus$', '/': 'm$div$', '*': 'm$mul$', '<': 'm$lt$', '<=': 'm$le$', '>': 'm$gt$', '>=': 'm$ge$', '<<': 'm$lshft$', '>>': 'm$rshft$', '|': 'm$or$', '&': 'm$and$', '^': 'm$xor$', '+@': 'm$uplus$', '-@': 'm$uminus$', '%': 'm$mod$', '**': 'm$pow$'};
var reverse_method_names = {}; for (var id in method_names) {
reverse_method_names[method_names[id]] = id;}
(function($opal) {var nil = $opal.nil, $const = $opal.constants, _a, $breaker = $opal.breaker, $no_proc = $opal.no_proc, $klass = $opal.klass, $defn = $opal.defn, $defs = $opal.defs, $const_get = $opal.const_get, $slice = $opal.slice;
($opal.gvars["$LOAD_PATH"] = ($opal.gvars["$:"] = LOADER_PATHS));


($opal.gvars["$~"] = nil);

$const.RUBY_ENGINE = "opal-browser";
$const.RUBY_PLATFORM = "opal";
$const.RUBY_VERSION = "1.9.2";
$const.ARGV = [];
$klass(this, nil, "Module", function() {var $const = this.$const, $proto = this.$proto; 
  $proto.m$eqq$ = function($yield, object) {

    return object.m$kind_of$p(null, this);};

  $proto.m$alias_method = function($yield, newname, oldname) {
    $opal.alias(this, newname, oldname);

    return this;
  };

  $proto.m$ancestors = function($yield) {

    
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

  $proto.m$append_features = function($yield, mod) {
    include_module(mod, this);

    return this;
  };

  $proto.m$attr_accessor = function($yield, attrs) {attrs = $slice.call(arguments, 1);

    
      for (var i = 0, length = attrs.length; i < length; i++) {
        define_attr(this, attrs[i], true, true);
      }

      return nil;
    };

  $proto.m$attr_accessor_bridge = function($yield, target, attrs) {attrs = $slice.call(arguments, 2);

    
      for (var i = 0, length = attrs.length; i < length; i++) {
        define_attr_bridge(this, target, attrs[i], true, true);
      }

      return nil;
    };

  $proto.m$attr_reader = function($yield, attrs) {attrs = $slice.call(arguments, 1);

    
      for (var i = 0, length = attrs.length; i < length; i++) {
        define_attr(this, attrs[i], true, false);
      }

      return nil;
    };

  $proto.m$attr_reader_bridge = function($yield, target, attrs) {attrs = $slice.call(arguments, 2);

    
      for (var i = 0, length = attrs.length; i < length; i++) {
        define_attr_bridge(this, target, attrs[i], true, false);
      }

      return nil;
    };

  $proto.m$attr_writer = function($yield, attrs) {attrs = $slice.call(arguments, 1);

    
      for (var i = 0, length = attrs.length; i < length; i++) {
        define_attr(this, attrs[i], false, true);
      }

      return nil;
    };

  $proto.m$attr_reader_bridge = function($yield, target, attrs) {attrs = $slice.call(arguments, 2);

    
      for (var i = 0, length = attrs.length; i < length; i++) {
        define_attr_bridge(this, target, attrs[i], false, true);
      }

      return nil;
    };

  $proto.m$attr = function($yield, name, setter) {if (setter === undefined) { setter = false; }
    define_attr(this, name, true, setter);

    return this;
  };

  $proto.m$attr_bridge = function($yield, target, name, setter) {if (setter === undefined) { setter = false; }
    define_attr_bridge(this, target, name, true, setter);

    return this;
  };

  $proto.m$define_method = function($yield, name) {var $block_given = ($yield != null); var body = $yield || ($yield = $no_proc, nil);var $context = $yield.$S;

    
      if (body === nil) {
        raise(RubyLocalJumpError, 'no block given');
      }

      define_method(this, mid_to_jsid(name), body);
      this.$methods.push(name);

      return nil;
    };

  $proto.m$define_method_bridge = function($yield, object, name, ali) {var _a; if (ali === undefined) { ali = nil; }

    
      define_method_bridge(this, object, mid_to_jsid((_a = ali, _a !== false && _a != nil ? _a : name)), name);
      this.$methods.push(name);

      return nil;
    };

  $proto.m$include = function($yield, mods) {var mod = nil; mods = $slice.call(arguments, 1);

    
      var i = mods.length - 1, mod;
      while (i >= 0) {
        mod = mods[i];
        mod.m$append_features(null, this);
        mod.m$included(null, this);

        i--;
      }

      return this;
    };

  $proto.m$instance_methods = function($yield) {

    return this.$methods;};

  $proto.m$included = function($yield, mod) {

    return nil;};

  $proto.m$module_eval = function($yield) {var $block_given = ($yield != null); var block = $yield || ($yield = $no_proc, nil);var $context = $yield.$S;

    
      if (block === nil) {
        raise(RubyLocalJumpError, 'no block given');
      }

      return block.call(this, null);
    };

  this.m$alias_method(null, "class_eval", "module_eval");

  $proto.m$name = function($yield) {

    return this.__classid__;};

  this.m$alias_method(null, "public_instance_methods", "instance_methods");

  return this.m$alias_method(null, "to_s", "name");
}, 0);
$klass(this, nil, "Class", function() {var $const = this.$const, $proto = this.$proto; 
  $defs(this, 'm$new', function($yield, sup) {var $block_given = ($yield != null); var block = $yield || ($yield = $no_proc, nil);var $context = $yield.$S;if (sup === undefined) { sup = $const.Object; }
    
      var klass             = boot_class(sup);
          klass.__classid__ = "AnonClass";

      make_metaclass(klass, sup.$klass);

      sup.m$inherited(null, klass);

      return block !== nil ? block.call(klass, null) : klass;
    
  });

  $proto.m$allocate = function($yield) {

    return new this.$allocator();};

  $proto.m$new = function($yield, args) {var obj = nil, _a, _b; var $block_given = ($yield != null); var block = $yield || ($yield = $no_proc, nil);var $context = $yield.$S;args = $slice.call(arguments, 1);
    obj = this.m$allocate();
    (_b=obj).m$initialize.apply(_b, [
    (_b = block, (typeof(_b) === 'function' || _b == nil ? _b : _b.m$to_proc()))].concat(args));
    return obj;};

  $proto.m$inherited = function($yield, cls) {
    return nil;};

  return $proto.m$superclass = function($yield) {

    
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

$klass(this, nil, "Kernel", function() {var $const = this.$const, $proto = this.$proto; 
  $proto.m$match$ = function($yield, obj) {

    return false;};

  $proto.m$eqq$ = function($yield, other) {

    return this == other;};

  $proto.m$Object = function($yield, object) {var _a, _b; 

    if ((_a = (!!(_b = object, _b == null || !_b.$klass))) !== false && _a !== nil) {return $opal.const_get(($const.Native).$const, "Object").m$new(null, object)} else {return object};};

  $proto.m$Array = function($yield, object) {var _a, _b; 


    if ((_a = object) !== false && _a !== nil) {} else {return []};if ((_a = (!!(_b = object, _b == null || !_b.$klass))) !== false && _a !== nil) {} else {
      if ((_a = object.m$respond_to$p(null, "to_ary")) !== false && _a !== nil) {return object.m$to_ary()
      };if ((_a = object.m$respond_to$p(null, "to_a")) !== false && _a !== nil) {return object.m$to_a()
      };};

    
      var length = object.length || 0,
          result = new Array(length);

      while (length--) {
        result[length] = object[length];
      }

      return result;
    
  };

  $proto.m$at_exit = function($yield) {var $block_given = ($yield != null); var block = $yield || ($yield = $no_proc, nil);var $context = $yield.$S;

    
      if (block === nil) {
        raise(RubyArgError, 'called without a block');
      }

      end_procs.push(block);

      return block;
    };

  $proto.m$class = function($yield) {

    return class_real(this.$klass);};

  $proto.m$define_singleton_method = function($yield) {var $block_given = ($yield != null); var body = $yield || ($yield = $no_proc, nil);var $context = $yield.$S;

    
      if (body === nil) {
        raise(RubyLocalJumpError, 'no block given');
      }

      $opal.ds(this, name, body);

      return this;
    };

  $proto.m$equal$p = function($yield, other) {

    return this === other;};

  $proto.m$extend = function($yield, mods) {mods = $slice.call(arguments, 1);

    
      for (var i = 0, length = mods.length; i < length; i++) {
        include_module(singleton_class(this), mods[i]);
      }

      return this;
    };

  $proto.m$hash = function($yield) {

    return this.$id;};

  $proto.m$inspect = function($yield) {

    return this.m$to_s();};

  $proto.m$instance_of$p = function($yield, klass) {

    return this.$klass === klass;};

  $proto.m$instance_variable_defined$p = function($yield, name) {

    this.hasOwnProperty(name.substr(1));};

  $proto.m$instance_variable_get = function($yield, name) {

    
      var ivar = this[name.substr(1)];

      return ivar == undefined ? nil : ivar;
    };

  $proto.m$instance_variable_set = function($yield, name, value) {

    return this[name.substr(1)] = value;};

  $proto.m$instance_variables = function($yield) {

    
      var result = [];

      for (var name in this) {
        result.push(name);
      }

      return result;
    };

  $proto.m$is_a$p = function($yield, klass) {

    
      var search = this.$klass;

      while (search) {
        if (search === klass) {
          return true;
        }

        search = search.$s;
      }

      return false;
    };

  this.m$alias_method(null, "kind_of?", "is_a?");

  $proto.m$lambda = function($yield) {var $block_given = ($yield != null); var block = $yield || ($yield = $no_proc, nil);var $context = $yield.$S;

    return block;};

  $proto.m$loop = function($yield) {var $block_given = ($yield != null); var block = $yield || ($yield = $no_proc, nil);var $context = $yield.$S;


    if ($block_given) {} else {return this.m$enum_for(null, "loop")};
      while (true) {
        if ($yield.call($context, null) === breaker) {
          return breaker.$v;
        }
      }

      return this;
    
  };

  $proto.m$nil$p = function($yield) {

    return false;};

  $proto.m$object_id = function($yield) {

    return this.$id || (this.$id = unique_id++);};

  $proto.m$print = function($yield, strs) {var _a, _b; strs = $slice.call(arguments, 1);

    return (_a=((_b = $opal.gvars["$stdout"]) == null ? nil : _b)).m$print.apply(_a, [null].concat(strs));};

  $proto.m$proc = function($yield) {var $block_given = ($yield != null); var block = $yield || ($yield = $no_proc, nil);var $context = $yield.$S;

    return block;};

  $proto.m$puts = function($yield, strs) {var _a, _b; strs = $slice.call(arguments, 1);

    return (_a=((_b = $opal.gvars["$stdout"]) == null ? nil : _b)).m$puts.apply(_a, [null].concat(strs));};

  $proto.m$raise = function($yield, exception, string) {var _a; if (string === undefined) { string = undefined; }

    
      if ((typeof exception === 'string')) {
        exception = (RubyRuntimeError).m$new(null, exception);
      }
      else if (((_a = exception.m$is_a$p(null, RubyException)) === false || _a === nil)) {
        exception = (exception).m$new(null, string);
      }

      throw exception;
    };

  $proto.m$rand = function($yield, max) {if (max === undefined) { max = undefined; }

    return max === undefined ? Math.random() : Math.floor(Math.random() * max);};

  $proto.m$require = function($yield, path) {

    
      var resolved = find_lib(path);

      if (!resolved) {
        raise(RubyLoadError, 'no such file to load -- ' + path);
      }

      if (LOADER_CACHE[resolved]) {
        return false;
      }

      LOADER_CACHE[resolved] = true;
      $opal.FILE = resolved;
      FACTORIES[resolved].call(top_self, resolved, $opal);

      return true;
    };

  $proto.m$respond_to$p = function($yield, name) {

    
      var meth = this[mid_to_jsid(name)];
      return !!meth;
    };

  $proto.m$singleton_class = function($yield) {

    return singleton_class(this);};

  $proto.m$tap = function($yield) {var $block_given = ($yield != null); var block = $yield || ($yield = $no_proc, nil);var $context = $yield.$S;

    
      if (block === nil) {
        raise(RubyLocalJumpError, 'no block given');
      }

      if ($yield.call($context, null, this) === breaker) {
        return breaker.$v;
      }

      return this;
    };

  $proto.m$to_s = function($yield) {

    return inspect_object(this);};;this.$donate(["m$match$", "m$eqq$", "m$Object", "m$Array", "m$at_exit", "m$class", "m$define_singleton_method", "m$equal$p", "m$extend", "m$hash", "m$inspect", "m$instance_of$p", "m$instance_variable_defined$p", "m$instance_variable_get", "m$instance_variable_set", "m$instance_variables", "m$is_a$p", "m$lambda", "m$loop", "m$nil$p", "m$object_id", "m$print", "m$proc", "m$puts", "m$raise", "m$rand", "m$require", "m$respond_to$p", "m$singleton_class", "m$tap", "m$to_s"]);
}, 1);

$klass(this, nil, "BasicObject", function() {var $const = this.$const, $proto = this.$proto; 
  $proto.m$initialize = function($yield) {
    return nil;};

  $proto.m$eq$ = function($yield, other) {

    return this === other;};

  $proto.m$__send__ = function($yield, symbol, args) {var $block_given = ($yield != null); var block = $yield || ($yield = $no_proc, nil);var $context = $yield.$S;args = $slice.call(arguments, 2);

    
      var meth = this[mid_to_jsid(symbol)];

      if (meth) {
        args.unshift(null);

        return meth.apply(this, args);
      }
      else {
        throw new Error("method missing yielder for " + symbol + " in __send__");
      }
    };

  $opal.alias(this, "send", "__send__");

  $opal.alias(this, "eql?", "==");
  $opal.alias(this, "equal?", "==");

  $proto.m$instance_eval = function($yield, string) {var $block_given = ($yield != null); var block = $yield || ($yield = $no_proc, nil);var $context = $yield.$S;if (string === undefined) { string = nil; }

    
      if (block === nil) {
        raise(RubyArgError, 'block not supplied');
      }

      return block.call(this, null, this);
    };

  $proto.m$instance_exec = function($yield, args) {var $block_given = ($yield != null); var block = $yield || ($yield = $no_proc, nil);var $context = $yield.$S;args = $slice.call(arguments, 1);

    
      if (block === nil) {
        raise(RubyArgError, 'block not supplied');
      }

      args.unshift(null);

      return block.apply(this, args);
    };

  $proto.m$method_missing = function($yield, symbol, args) {args = $slice.call(arguments, 2);

    return raise(RubyNoMethodError, 'undefined method `' + symbol + '` for ' + this.m$inspect());};

  $proto.m$singleton_method_added = function($yield, symbol) {

    return nil;};

  $proto.m$singleton_method_removed = function($yield, symbol) {

    return nil;};

  $proto.m$singleton_method_undefined = function($yield, symbol) {

    return nil;};;this.$donate(["m$initialize", "m$eq$", "m$__send__", "m$instance_eval", "m$instance_exec", "m$method_missing", "m$singleton_method_added", "m$singleton_method_removed", "m$singleton_method_undefined"]);
}, 0);

$klass(this, nil, "Object", function() {var $const = this.$const, $proto = this.$proto; 


  this.m$include(null, $const.Kernel);$proto.m$methods = function($yield) {

    return this.$klass.$methods;};

  this.m$alias_method(null, "private_methods", "methods");

  this.m$alias_method(null, "protected_methods", "methods");

  this.m$alias_method(null, "public_methods", "methods");

  $proto.m$singleton_methods = function($yield) {

    return this.m$raise(null, $const.NotImplementedError, "Object#singleton_methods not yet implemented");};

  $proto.m$to_native = function($yield) {

    return this.m$raise(null, $const.TypeError, "no specialized #to_native has been implemented");};;this.$donate(["m$methods", "m$singleton_methods", "m$to_native"]);
}, 0);

$defs(this, 'm$to_s', function(
  $yield) {return "main"
});

$defs(this, 'm$include', function($yield, mod) {
  return $const.Object.m$include(
  null, mod)});

$klass(this, nil, "Boolean", function() {var $const = this.$const, $proto = this.$proto; 
  $proto.m$and$ = function($yield, other) {

    return this.valueOf() ? (other !== false && other !== nil) : false;};

  $proto.m$or$ = function($yield, other) {

    return this.valueOf() ? true : (other !== false && other !== nil);};

  $proto.m$xor$ = function($yield, other) {

    return this.valueOf() ? (other === false || other === nil) : (other !== false && other !== nil);};

  $proto.m$eq$ = function($yield, other) {

    return this.valueOf() === other.valueOf();};

  $proto.m$class = function($yield) {

    return this.valueOf() ? $const.TrueClass : $const.FalseClass;};

  $proto.m$to_native = function($yield) {

    return this.valueOf();};

  return $proto.m$to_s = function($yield) {

    return this.valueOf() ? 'true' : 'false';};
}, 0);

$klass(this, nil, "TrueClass", function() {var $const = this.$const, $proto = this.$proto; 
  return $defs(this, 'm$eqq$', function($yield, obj) {
    return obj === true;
  })
}, 0);

$klass(this, nil, "FalseClass", function() {var $const = this.$const, $proto = this.$proto; 
  return $defs(this, 'm$eqq$', function($yield, obj) {
    return obj === false;
  })
}, 0);

$const.TRUE = true;
$const.FALSE = false;

$klass(this, nil, "NilClass", function() {var $const = this.$const, $proto = this.$proto; 
  $proto.m$and$ = function($yield, other) {

    return false;};

  $proto.m$or$ = function($yield, other) {

    return other !== false && other !== nil;};

  $proto.m$xor$ = function($yield, other) {

    return other !== false && other !== nil;};

  $proto.m$eq$ = function($yield, other) {

    return this === other;};

  $proto.m$inspect = function($yield) {

    return "nil";};

  $proto.m$nil$p = function($yield) {

    return true;};

  $proto.m$to_a = function($yield) {

    return [];};

  $proto.m$to_i = function($yield) {

    return 0;};

  $proto.m$to_f = function($yield) {

    return 0.0;};

  $proto.m$to_native = function($yield) {

    var result; return result;};

  return $proto.m$to_s = function($yield) {

    return "";};
}, 0);

$const.NIL = nil;

$klass(this, nil, "Native", function() {var $const = this.$const, $proto = this.$proto; 
  $klass(this, nil, "Object", function() {var $const = this.$const, $proto = this.$proto; 


    this.m$include(null, $const.Native);$proto.m$aref$ = function($yield, name) {this['native'] == null && (this['native'] = nil);

      return this['native'][name];};

    $proto.m$aset$ = function($yield, name, value) {this['native'] == null && (this['native'] = nil);

      return this['native'][name] = value;};

    $proto.m$nil$p = function($yield) {this['native'] == null && (this['native'] = nil);

      return this['native'] === null || this['native'] === undefined;};

    $proto.m$method_missing = function($yield, name, args) {var _a, _b; this['native'] == null && (this['native'] = nil);args = $slice.call(arguments, 2);
      if ((_a = (typeof this['native'][name] === 'function')) !== false && _a !== nil) {} else {return $opal.zuper(arguments.callee, this, [])

      };return (_a=this).m$__native_send__.apply(_a, [null, name].concat(
      args));};;this.$donate(["m$aref$", "m$aset$", "m$nil$p", "m$method_missing"]);
  }, 0);

  $defs(this, 'm$included', function($yield, klass) {
    return $klass(
    klass, nil, nil, function() {var $const = this.$const; return $defn(this, 'm$from_native', function($yield, object) {var instance = nil; 
      instance = 
      this.m$allocate();instance.m$instance_variable_set(null, "@native", 

      object);
      return instance;})}, 2)

  });

  $proto.m$initialize = function($yield, native$) {

    return this['native'] = native$;};

  $proto.m$to_native = function($yield) {this['native'] == null && (this['native'] = nil);

    return this['native'];};

  $proto.m$native_send = function($yield, name, args) {var _a, _b; this['native'] == null && (this['native'] = nil);args = $slice.call(arguments, 2);
    if ((_a = (typeof this['native'][name] === 'function')) !== false && _a !== nil) {} else {return (_a=this).m$method_missing.apply(_a, [null, name].concat(args))

    };return this['native'][name].apply(this['native'], args);
  };

  this.m$alias_method(null, "__native_send__", "native_send");;this.$donate(["m$initialize", "m$to_native", "m$native_send"]);
}, 1);

$klass(this, nil, "Enumerable", function() {var $const = this.$const, $proto = this.$proto; 
  $proto.m$all$p = function($yield) {var $block_given = ($yield != null); var block = $yield || ($yield = $no_proc, nil);var $context = $yield.$S;

    
      var result = true;

      if (block !== nil) {
        this.m$each(function (iter, obj) {
          var value;

          if ((value = $yield.call($context, null, obj)) === $breaker) {
            return $breaker.$v;
          }

          if (value === false || value === nil) {
            result      = false;
            $breaker.$v = nil;

            return $breaker;
          }
        });
      }
      else {
        this.m$each(function (iter, obj) {
          if (obj === false || obj === nil) {
            result      = false;
            $breaker.$v = nil;

            return $breaker;
          }
        });
      }

      return result;
    };

  $proto.m$any$p = function($yield) {var $block_given = ($yield != null); var block = $yield || ($yield = $no_proc, nil);var $context = $yield.$S;

    
      var result = false, proc;

      if (block !== nil) {
        this.m$each(function (iter, obj) {
          var value;

          if ((value = $yield.call($context, null, obj)) === $breaker) {
            return $breaker.$v;
          }

          if (value !== false && value !== nil) {
            result      = true;
            $breaker.$v = nil;

            return $breaker;
          }
        });
      }
      else {
        this.m$each(function (iter, obj) {
          if (obj !== false && obj !== nil) {
            result      = true;
            $breaker.$v = nil;

            return $breaker;
          }
        });
      }

      return result;
    };

  $proto.m$collect = function($yield) {var $block_given = ($yield != null); var block = $yield || ($yield = $no_proc, nil);var $context = $yield.$S;


    if ($block_given) {} else {return this.m$enum_for(null, "collect")};
      var result = [];

      this.m$each(function () {
        var obj = $slice.call(arguments, 1),
            value;

        if ((value = $yield.apply($context, [null].concat(obj))) === $breaker) {
          return $breaker.$v;
        }

        result.push(value);
      });

      return result;
    
  };

  $proto.m$count = function($yield, object) {var $block_given = ($yield != null); var block = $yield || ($yield = $no_proc, nil);var $context = $yield.$S;if (object === undefined) { object = undefined; }

    
      var result = 0;

      if (block === nil) {
        if (object === undefined) {
          $yield = function () { return true; };
        }
        else {
          $yield = function (iter, obj) { return (obj).m$eq$(null, object); };
        }
      }

      this.m$each(function (iter, obj) {
        var value;

        if ((value = $yield.call($context, null, obj)) === $breaker) {
          return $breaker.$v;
        }

        if (value !== false && value !== nil) {
          result++;
        }
      });

      return result;
    };

  $proto.m$detect = function($yield, ifnone) {var _a; var $block_given = ($yield != null); var block = $yield || ($yield = $no_proc, nil);var $context = $yield.$S;if (ifnone === undefined) { ifnone = undefined; }


    if ((_a = block) !== false && _a !== nil) {} else {return this.m$enum_for(null, "detect", ifnone)};
      var result = nil;

      this.m$each(function(iter, obj) {
        var value;

        if ((value = $yield.call($context, null, obj)) === $breaker) {
          return $breaker.$v;
        }

        if (value !== false && value !== nil) {
          result      = obj;
          $breaker.$v = nil;

          return $breaker;
        }
      });

      if (result !== nil) {
        return result;
      }

      if ((typeof ifnone === 'function')) {
        return ifnone.m$call(null);
      }

      return ifnone === undefined ? nil : ifnone;
    
  };

  $proto.m$drop = function($yield, number) {


    this.m$raise(null, $const.NotImplementedError);
      var result  = [],
          current = 0;

      this.m$each(function(iter, obj) {
        if (number < current) {
          result.push(e);
        }

        current++;
      });

      return result;
    
  };

  $proto.m$drop_while = function($yield) {var _a; var $block_given = ($yield != null); var block = $yield || ($yield = $no_proc, nil);var $context = $yield.$S;


    if ((_a = block) !== false && _a !== nil) {} else {return this.m$enum_for(null, "drop_while")};
      var result = [];

      this.m$each(function (iter, obj) {
        var value;

        if ((value = $yield.call($context, null, obj)) === $breaker) {
          return $breaker.$v;
        }

        if (value !== false && value !== nil) {
          result.push(obj);
        }
        else {
          return $breaker;
        }
      });

      return result;
    
  };

  $proto.m$each_with_index = function($yield) {var _a; var $block_given = ($yield != null); var block = $yield || ($yield = $no_proc, nil);var $context = $yield.$S;


    if ((_a = block) !== false && _a !== nil) {} else {return this.m$enum_for(null, "each_with_index")};
      var index = 0;

      this.m$each(function (iter, obj) {
        var value;

        if ((value = $yield.call($context, null, obj, index)) === $breaker) {
          return $breaker.$v;
        }

        index++;
      });

      return nil;
    
  };

  $proto.m$entries = function($yield) {

    
      var result = [];

      this.m$each(function (iter, obj) { return result.push(obj); })

      return result;
    };

  this.m$alias_method(null, "find", "detect");

  $proto.m$find_index = function($yield, object) {var _a; var $block_given = ($yield != null); var block = $yield || ($yield = $no_proc, nil);var $context = $yield.$S;if (object === undefined) { object = undefined; }


    if ((_a = block) !== false && _a !== nil) {} else {return this.m$enum_for(null, "find_index", object)};
      if (object !== undefined) {
        $yield = function (iter, obj) { return obj.m$eq$(object); };
      }

      var result = nil;

      this.m$each_with_index(function(iter, obj, index) {
        var value;

        if ((value = $yield.call($context, null, obj)) === $breaker) {
          return $breaker.$v;
        }

        if (value !== false && value !== nil) {
          result     = obj;
          breaker.$v = index;

          return $breaker;
        }
      });

      return result;
    
  };

  $proto.m$first = function($yield, number) {if (number === undefined) { number = undefined; }

    
      var result = [],
          current = 0;

      if (number === undefined) {
        this.m$each(function (iter, obj) { result = obj; return $breaker; });
      }
      else {
        this.m$each(function (iter, obj) {
          if (number < current) {
            return $breaker;
          }

          result.push(obj);

          current++;
        });
      }

      return result;
    };

  $proto.m$grep = function($yield, pattern) {var $block_given = ($yield != null); var block = $yield || ($yield = $no_proc, nil);var $context = $yield.$S;

    
      var result = [];

      if (block !== nil) {
        this.m$each(function (iter, obj) {
          var value = pattern.m$eqq$(obj);

          if (value !== false && value !== nil) {
            if ((value = $yield.call($context, null, obj)) === $breaker) {
              return $breaker.$v;
            }

            result.push(obj);
          }
        });
      }
      else {
        this.m$each(function (iter, obj) {
          var value = pattern.m$eqq$(obj);

          if (value !== false && value !== nil) {
            ary.push(obj);
          }
        });
      }

      return result;
    };

  this.m$alias_method(null, "to_a", "entries");;this.$donate(["m$all$p", "m$any$p", "m$collect", "m$count", "m$detect", "m$drop", "m$drop_while", "m$each_with_index", "m$entries", "m$find_index", "m$first", "m$grep"]);
}, 1);

$klass(this, nil, "Comparable", function() {var $const = this.$const, $proto = this.$proto; 
  $proto.m$lt$ = function($yield, other) {

    return this.m$cmp$(null, other).m$eq$(null, -1);};

  $proto.m$le$ = function($yield, other) {var _a, _b; 

    return (_a = this.m$cmp$(null, other), _b = 0, typeof(_a) === 'number' ? _a <= _b : _a.m$le$(null, _b));};

  $proto.m$eq$ = function($yield, other) {

    return this.m$cmp$(null, other).m$eq$(null, 0);};

  $proto.m$gt$ = function($yield, other) {

    return this.m$cmp$(null, other).m$eq$(null, 1);};

  $proto.m$ge$ = function($yield, other) {var _a, _b; 

    return (_a = this.m$cmp$(null, other), _b = 0, typeof(_a) === 'number' ? _a >= _b : _a.m$ge$(null, _b));};

  $proto.m$between$p = function($yield, min, max) {var _a, _b, _c; 

    return (_a = (_b = this, _c = min, typeof(_b) === 'number' ? _b > _c : _b.m$gt$(null, _c)) ? (_c = this, _b = max, typeof(_c) === 'number' ? _c < _b : _c.m$lt$(null, _b)) : _a);};;this.$donate(["m$lt$", "m$le$", "m$eq$", "m$gt$", "m$ge$", "m$between$p"]);
}, 1);



$klass(this, nil, "Enumerator", function() {var $const = this.$const, $proto = this.$proto; 


  this.m$include(null, $const.Enumerable);$klass(this, nil, "Yielder", function() {var $const = this.$const, $proto = this.$proto; 
    $proto.m$initialize = function($yield, block) {

      return this.block = block;};

    $proto.m$call = function($yield, block) {this.block == null && (this.block = nil);
      this.call = 

      block;return this.block.m$call();
    };

    $proto.m$yield = function($yield, value) {this.call == null && (this.call = nil);

      return this.call.m$call(null, value);};

    return this.m$alias_method(null, "<<", "yield");
  }, 0);

  $klass(this, nil, "Generator", function() {var $const = this.$const, $proto = this.$proto; 
    this.m$attr_reader(null, "enumerator");

    $proto.m$initialize = function($yield, block) {

      return this.yielder = $const.Yielder.m$new(null, block);};

    return $proto.m$each = function($yield) {this.yielder == null && (this.yielder = nil);var $block_given = ($yield != null); var block = $yield || ($yield = $no_proc, nil);var $context = $yield.$S;

      return this.yielder.m$call(null, block);};
  }, 0);

  $proto.m$initialize = function($yield, object, method, args) {var _a; var $block_given = ($yield != null); var block = $yield || ($yield = $no_proc, nil);var $context = $yield.$S;if (object === undefined) { object = nil; }if (method === undefined) { method = "each"; }args = $slice.call(arguments, 3);

    if ($block_given) {this.object = $const.Generator.m$new(null, block);
      method = "each";
    };



    if ((_a = object) !== false && _a !== nil) {} else {this.m$raise(null, $const.ArgumentError, "wrong number of argument (0 for 1+)")};this.object = 
    object;this.method = 
    method;this.args = 

    args;return this.current = 0;
  };

  $proto.m$next = function($yield) {
    return nil;};

  $proto.m$each = function($yield) {var _a, _b; this.object == null && (this.object = nil);this.method == null && (this.method = nil);var $block_given = ($yield != null); var block = $yield || ($yield = $no_proc, nil);var $context = $yield.$S;


    if ((_a = block) !== false && _a !== nil) {} else {return this};return (_b=this.object).m$__send__.apply(_b, [
    (_b = block, (typeof(_b) === 'function' || _b == nil ? _b : _b.m$to_proc())), this.method].concat(this.m$args()));};

  $proto.m$each_with_index = function($yield) {var _a, _b; var $block_given = ($yield != null); var block = $yield || ($yield = $no_proc, nil);var $context = $yield.$S;

    return this.m$with_index((_b = block, (typeof(_b) === 'function' || _b == nil ? _b : _b.m$to_proc())));};

  $proto.m$with_index = function($yield, offset) {var _a; var $block_given = ($yield != null); var block = $yield || ($yield = $no_proc, nil);var $context = $yield.$S;if (offset === undefined) { offset = 0; }

    if ((_a = block) !== false && _a !== nil) {return nil} else {return $const.Enumerator.m$new(null, this, "with_index", offset)};};

  return $proto.m$with_object = function($yield, object) {var _a; var $block_given = ($yield != null); var block = $yield || ($yield = $no_proc, nil);var $context = $yield.$S;


    if ((_a = block) !== false && _a !== nil) {return nil} else {return $const.Enumerator.m$new(null, this, "with_object", object)};};
}, 0);

$klass(this, nil, "Kernel", function() {var $const = this.$const, $proto = this.$proto; 
  $proto.m$enum_for = function($yield, method, args) {var _a; if (method === undefined) { method = "each"; }args = $slice.call(arguments, 2);

    return (_a=$const.Enumerator).m$new.apply(_a, [null, this, method].concat(args));};

  this.m$alias_method(null, "to_enum", "enum_for");;this.$donate(["m$enum_for"]);
}, 1);

$klass(this, nil, "Array", function() {var $const = this.$const, $proto = this.$proto; 


  this.m$include(null, $const.Enumerable);$defs(this, 'm$aref$', function($yield, objects) {objects = $slice.call(arguments, 1);
    
      var result = this.m$allocate();

      result.splice.apply(result, [0, 0].concat(objects));

      return result;
    
  });

  $defs(this, 'm$allocate', function(
    $yield) {
      var array        = [];
          array.$klass = this;

      return array;
    
  });

  $defs(this, 'm$new', function($yield, a) {a = $slice.call(arguments, 1);
    return [];
  });

  $proto.m$and$ = function($yield, other) {

    
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

  $proto.m$mul$ = function($yield, other) {var _a; 

    
      if ((typeof other === 'string')) {
        return this.join(other);
      }

      var result = [];

      for (var i = 0, length = this.length; i < length; i++) {
        result = result.concat(this);
      }

      return result;
    };

  $proto.m$plus$ = function($yield, other) {

    return this.slice(0).concat(other.slice(0));};

  $proto.m$lshft$ = function($yield, object) {
    this.push(object);

    return this;
  };

  $proto.m$cmp$ = function($yield, other) {

    
      if (this.m$hash() === other.m$hash()) {
        return 0;
      }

      if (this.length != other.length) {
        return (this.length > other.length) ? 1 : -1;
      }

      for (var i = 0, length = this.length, tmp; i < length; i++) {
        if ((tmp = (this[i]).m$cmp$(null, other[i])) !== 0) {
          return tmp;
        }
      }

      return 0;
    };

  $proto.m$eq$ = function($yield, other) {

    
      if (this.length !== other.length) {
        return false;
      }

      for (var i = 0, length = this.length; i < length; i++) {
        if (!(this[i]).m$eq$(null, other[i])) {
          return false;
        }
      }

      return true;
    };


  $proto.m$aref$ = function($yield, index, length) {if (length === undefined) { length = undefined; }

    
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


  $proto.m$aset$ = function($yield, index, value) {

    
      var size = this.length;

      if (index < 0) {
        index += size;
      }

      return this[index] = value;
    };

  $proto.m$assoc = function($yield, object) {

    
      for (var i = 0, length = this.length, item; i < length; i++) {
        if (item = this[i], item.length && (item[0]).m$eq$(null, object)) {
          return item;
        }
      }

      return nil;
    };

  $proto.m$at = function($yield, index) {

    
      if (index < 0) {
        index += this.length;
      }

      if (index < 0 || index >= this.length) {
        return nil;
      }

      return this[index];
    };

  $proto.m$clear = function($yield) {
    this.splice(0);

    return this;
  };

  $proto.m$clone = function($yield) {

    return this.slice(0);};

  $proto.m$collect = function($yield) {var $block_given = ($yield != null); var block = $yield || ($yield = $no_proc, nil);var $context = $yield.$S;


    if ($block_given) {} else {return this.m$enum_for(null, "collect")};
      var result = [];

      for (var i = 0, length = this.length, value; i < length; i++) {
        if ((value = $yield.call($context, null, this[i])) === $breaker) {
          return $breaker.$v;
        }

        result.push(value);
      }

      return result;
    
  };

  $proto.m$collect$b = function($yield) {var $block_given = ($yield != null); var block = $yield || ($yield = $no_proc, nil);var $context = $yield.$S;


    if ($block_given) {} else {return this.m$enum_for(null, "collect!")};
      for (var i = 0, length = this.length, val; i < length; i++) {
        if ((val = $yield.call($context, null, this[i])) === $breaker) {
          return $breaker.$v;
        }

        this[i] = val;
      }
    

    return this;
  };

  $proto.m$compact = function($yield) {

    
      var result = [];

      for (var i = 0, length = this.length, item; i < length; i++) {
        if ((item = this[i]) !== nil) {
          result.push(item);
        }
      }

      return result;
    };

  $proto.m$compact$b = function($yield) {

    
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

  $proto.m$concat = function($yield, other) {
    
      for (var i = 0, length = other.length; i < length; i++) {
        this.push(other[i]);
      }
    

    return this;
  };

  $proto.m$count = function($yield, object) {if (object === undefined) { object = undefined; }

    
      if (object === undefined) {
        return this.length;
      }

      var result = 0;

      for (var i = 0, length = this.length; i < length; i++) {
        if ((this[i]).m$eq$(null, object)) {
          result++;
        }
      }

      return result;
    };

  $proto.m$delete = function($yield, object) {

    
      var original = this.length;

      for (var i = 0, length = original; i < length; i++) {
        if ((this[i]).m$eq$(null, object)) {
          this.splice(i, 1);

          length--;
          i--;
        }
      }

      return this.length === original ? nil : object;
    };

  $proto.m$delete_at = function($yield, index) {

    
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

  $proto.m$delete_if = function($yield) {var $block_given = ($yield != null); var block = $yield || ($yield = $no_proc, nil);var $context = $yield.$S;


    if ($block_given) {} else {return this.m$enum_for(null, "delete_if")};
      for (var i = 0, length = this.length, value; i < length; i++) {
        if ((value = $yield.call($context, null, this[i])) === $breaker) {
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

  $proto.m$drop = function($yield, number) {

    return number > this.length ? [] : this.slice(number);};

  $proto.m$drop_while = function($yield) {var $block_given = ($yield != null); var block = $yield || ($yield = $no_proc, nil);var $context = $yield.$S;


    if ($block_given) {} else {return this.m$enum_for(null, "drop_while")};
      for (var i = 0, length = this.length, value; i < length; i++) {
        if ((value = $yield.call($context, null, this[i])) === $breaker) {
          return $breaker.$v;
        }

        if (value === false || value === nil) {
          return this.slice(i);
        }
      }

      return [];
    
  };

  $proto.m$each = function($yield) {var $block_given = ($yield != null); var block = $yield || ($yield = $no_proc, nil);var $context = $yield.$S;


    if ($block_given) {} else {return this.m$enum_for(null, "each")};
      for (var i = 0, length = this.length; i < length; i++) {
        if ($yield.call($context, null, this[i]) === $breaker) {
          return $breaker.$v;
        }
      }
    

    return this;
  };

  $proto.m$each_index = function($yield) {var $block_given = ($yield != null); var block = $yield || ($yield = $no_proc, nil);var $context = $yield.$S;


    if ($block_given) {} else {return this.m$enum_for(null, "each_index")};
      for (var i = 0, length = this.length; i < length; i++) {
        if ($yield.call($context, null, i) === $breaker) {
          return $breaker.$v;
        }
      }
    

    return this;
  };

  $proto.m$each_with_index = function($yield) {var $block_given = ($yield != null); var block = $yield || ($yield = $no_proc, nil);var $context = $yield.$S;


    if ($block_given) {} else {return this.m$enum_for(null, "each_with_index")};
      for (var i = 0, length = this.length; i < length; i++) {
        if ($yield.call($context, null, this[i], i) === $breaker) {
          return $breaker.$v;
        }
      }
    

    return this;
  };

  $proto.m$empty$p = function($yield) {

    return this.length === 0;};

  $proto.m$fetch = function($yield, index, defaults) {var $block_given = ($yield != null); var block = $yield || ($yield = $no_proc, nil);var $context = $yield.$S;if (defaults === undefined) { defaults = undefined; }

    
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
        return $yield.call($context, null, original);
      }

      raise(RubyIndexError, 'Array#fetch');
    };

  $proto.m$first = function($yield, count) {if (count === undefined) { count = undefined; }

    
      if (count !== undefined) {
        return this.slice(0, count);
      }

      return this.length === 0 ? nil : this[0];
    };

  $proto.m$flatten = function($yield, level) {if (level === undefined) { level = undefined; }

    
      var result = [];

      for (var i = 0, length = this.length, item; i < length; i++) {
        item = this[i];

        if (item.$flags & T_ARRAY) {
          if (level === undefined) {
            result = result.concat((item).m$flatten());
          }
          else if (level === 0) {
            result.push(item);
          }
          else {
            result = result.concat((item).m$flatten(null, level - 1));
          }
        }
        else {
          result.push(item);
        }
      }

      return result;
    };

  $proto.m$flatten$b = function($yield, level) {if (level === undefined) { level = undefined; }

    
      var flattenable = false;

      for (var i = 0, length = this.length; i < length; i++) {
        if (this[i].$flags & T_ARRAY) {
          flattenable = true;

          break;
        }
      }

      return flattenable ? this.m$replace(null, this.m$flatten(null, level)) : nil;
    };

  $proto.m$grep = function($yield, pattern) {

    
      var result = [];

      for (var i = 0, length = this.length, item; i < length; i++) {
        item = this[i];

        if (pattern.m$eqq$(null, item)) {
          result.push(item);
        }
      }

      return result;
    };

  $proto.m$hash = function($yield) {

    return this.$id || (this.$id = unique_id++);};

  $proto.m$include$p = function($yield, member) {

    
      for (var i = 0, length = this.length; i < length; i++) {
        if ((this[i]).m$eq$(null, member)) {
          return true;
        }
      }

      return false;
    };

  $proto.m$index = function($yield, object) {var _a, _b; var $block_given = ($yield != null); var block = $yield || ($yield = $no_proc, nil);var $context = $yield.$S;if (object === undefined) { object = undefined; }
    if ((_a = (_b = $block_given ? object.m$eq$(

    null, undefined) : _b)) !== false && _a !== nil) {} else {return this.m$enum_for(null, "index")};
      if (block !== nil) {
        for (var i = 0, length = this.length, value; i < length; i++) {
          if ((value = $yield.call($context, null, this[i])) === $breaker) {
            return $breaker.$v;
          }

          if (value !== false && value !== nil) {
            return i;
          }
        }
      }
      else {
        for (var i = 0, length = this.length; i < length; i++) {
          if ((this[i]).m$eq$(null, object)) {
            return i;
          }
        }
      }

      return nil
    
  };

  $proto.m$inject = function($yield, initial) {var $block_given = ($yield != null); var block = $yield || ($yield = $no_proc, nil);var $context = $yield.$S;if (initial === undefined) { initial = undefined; }


    if ($block_given) {} else {return this.m$enum_for(null, "inject")};
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
        if ((value = $yield.call($context, null, result, this[i])) === $breaker) {
          return $breaker.$v;
        }

        result = value;
      }

      return result;
    
  };

  $proto.m$insert = function($yield, index, objects) {objects = $slice.call(arguments, 2);
    
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

  $proto.m$inspect = function($yield) {

    
      var inspect = [];

      for (var i = 0, length = this.length; i < length; i++) {
        inspect.push((this[i]).m$inspect());
      }

      return '[' + inspect.join(', ') + ']';
    };

  $proto.m$join = function($yield, sep) {if (sep === undefined) { sep = ""; }

    
      var result = [];

      for (var i = 0, length = this.length; i < length; i++) {
        result.push((this[i]).m$to_s());
      }

      return result.join(sep);
    };

  $proto.m$keep_if = function($yield) {var $block_given = ($yield != null); var block = $yield || ($yield = $no_proc, nil);var $context = $yield.$S;

    if ($block_given) {} else {return this.m$enum_for(null, "keep_if")};
      for (var i = 0, length = this.length, value; i < length; i++) {
        if ((value = $yield.call($context, null, this[i])) === $breaker) {
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

  $proto.m$last = function($yield, count) {if (count === undefined) { count = undefined; }

    
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

  $proto.m$length = function($yield) {

    return this.length;};

  this.m$alias_method(null, "map", "collect");

  this.m$alias_method(null, "map!", "collect!");

  $proto.m$pop = function($yield, count) {if (count === undefined) { count = undefined; }

    
      var length = this.length;

      if (count === undefined) {
        return length === 0 ? nil : this.pop();
      }

      if (count < 0) {
        raise(RubyArgError, 'negative count given');
      }

      return count > length ? this.splice(0) : this.splice(length - count, length);
    };

  $proto.m$push = function($yield, objects) {objects = $slice.call(arguments, 1);
    
      for (var i = 0, length = objects.length; i < length; i++) {
        this.push(objects[i]);
      }
    

    return this;
  };

  $proto.m$rassoc = function($yield, object) {

    
      for (var i = 0, length = this.length, item; i < length; i++) {
        item = this[i];

        if (item.length && item[1] !== undefined) {
          if ((item[1]).m$eq$(null, object)) {
            return item;
          }
        }
      }

      return nil;
    };

  $proto.m$reject = function($yield) {var $block_given = ($yield != null); var block = $yield || ($yield = $no_proc, nil);var $context = $yield.$S;


    if ($block_given) {} else {return this.m$enum_for(null, "reject")};
      var result = [];

      for (var i = 0, length = this.length, value; i < length; i++) {
        if ((value = $yield.call($context, null, this[i])) === $breaker) {
          return $breaker.$v;
        }

        if (value === false || value === nil) {
          result.push(this[i]);
        }
      }
      return result;
    
  };

  $proto.m$reject$b = function($yield) {var $block_given = ($yield != null); var block = $yield || ($yield = $no_proc, nil);var $context = $yield.$S;


    if ($block_given) {} else {return this.m$enum_for(null, "reject!")};
      var original = this.length;

      for (var i = 0, length = this.length, value; i < length; i++) {
        if ((value = $yield.call($context, null, this[i])) === $breaker) {
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

  $proto.m$replace = function($yield, other) {

    this.m$clear();
    return this.m$concat(null, other);};

  $proto.m$reverse = function($yield) {

    return this.reverse();};

  $proto.m$reverse$b = function($yield) {

    return this.m$replace(null, this.m$reverse());};

  $proto.m$reverse_each = function($yield) {var _a, _b; var $block_given = ($yield != null); var block = $yield || ($yield = $no_proc, nil);var $context = $yield.$S;


    if ($block_given) {} else {return this.m$enum_for(null, "reverse_each")};this.m$reverse().m$each(

    (_b = block, (typeof(_b) === 'function' || _b == nil ? _b : _b.m$to_proc())));return this;
  };

  $proto.m$rindex = function($yield, object) {var _a, _b; var $block_given = ($yield != null); var block = $yield || ($yield = $no_proc, nil);var $context = $yield.$S;if (object === undefined) { object = undefined; }
    if ((_a = (_b = $block_given ? object.m$eq$(

    null, undefined) : _b)) !== false && _a !== nil) {} else {return this.m$enum_for(null, "rindex")};
      if (block !== nil) {
        for (var i = this.length - 1, value; i >= 0; i--) {
          if ((value = $yield.call($context, null, this[i])) === $breaker) {
            return $breaker.$v;
          }

          if (value !== false && value !== nil) {
            return i;
          }
        }
      }
      else {
        for (var i = this.length - 1; i >= 0; i--) {
          if ((this[i]).m$eq$(null, object)) {
            return i;
          }
        }
      }

      return nil;
    
  };

  $proto.m$select = function($yield) {var $block_given = ($yield != null); var block = $yield || ($yield = $no_proc, nil);var $context = $yield.$S;


    if ($block_given) {} else {return this.m$enum_for(null, "select")};
      var result = [];

      for (var i = 0, length = this.length, item, value; i < length; i++) {
        item = this[i];

        if ((value = $yield.call($context, null, item)) === $breaker) {
          return $breaker.$v;
        }

        if (value !== false && value !== nil) {
          result.push(item);
        }
      }

      return result;
    
  };

  $proto.m$select$b = function($yield) {var $block_given = ($yield != null); var block = $yield || ($yield = $no_proc, nil);var $context = $yield.$S;

    if ($block_given) {} else {return this.m$enum_for(null, "select!")};
      var original = this.length;

      for (var i = 0, length = original, item, value; i < length; i++) {
        item = this[i];

        if ((value = $yield.call($context, null, item)) === $breaker) {
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

  $proto.m$shift = function($yield, count) {if (count === undefined) { count = undefined; }

    return count === undefined ? this.shift() : this.splice(0, count);};

  this.m$alias_method(null, "size", "length");

  this.m$alias_method(null, "slice", "[]");

  $proto.m$slice$b = function($yield, index, length) {if (length === undefined) { length = undefined; }

    
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

  $proto.m$take = function($yield, count) {

    return this.slice(0, count);};

  $proto.m$take_while = function($yield) {var $block_given = ($yield != null); var block = $yield || ($yield = $no_proc, nil);var $context = $yield.$S;


    if ($block_given) {} else {return this.m$enum_for(null, "take_while")};
      var result = [];

      for (var i = 0, length = this.length, item, value; i < length; i++) {
        item = this[i];

        if ((value = $yield.call($context, null, item)) === $breaker) {
          return $breaker.$v;
        }

        if (value === false || value === nil) {
          return result;
        }

        result.push(item);
      }

      return result;
    
  };

  $proto.m$to_a = function($yield) {

    return this;};

  this.m$alias_method(null, "to_ary", "to_a");

  $proto.m$to_native = function($yield) {var _a; 

    return this.m$map((_a=function(_$, obj) {var _a, _b; if (obj === undefined) {obj = nil; }if ((_a = (!!(_b = obj, _b != null && _b.$klass))) !== false && _a !== nil) {return obj.m$to_native()} else {return obj}},_a.$S=this,_a));};

  this.m$alias_method(null, "to_s", "inspect");

  $proto.m$uniq = function($yield) {

    
      var result = [],
          seen   = {};

      for (var i = 0, length = this.length, item, hash; i < length; i++) {
        item = this[i];
        hash = this.m$item().m$hash();

        if (!seen[hash]) {
          seen[hash] = true;

          result.push(item);
        }
      }

      return result;
    };

  $proto.m$uniq$b = function($yield) {

    
      var original = this.length,
          seen     = {};

      for (var i = 0, length = original, item, hash; i < length; i++) {
        item = this[i];
        hash = this.m$item().m$hash();

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

  return $proto.m$unshift = function($yield, objects) {objects = $slice.call(arguments, 1);

    
      for (var i = 0, length = objects.length; i < length; i++) {
        this.unshift(objects[i]);
      }

      return this;
    };
}, 0);

$klass(this, nil, "Hash", function() {var $const = this.$const, $proto = this.$proto; 


  this.m$include(null, $const.Enumerable);$defs(this, 'm$aref$', function($yield, objs) {objs = $slice.call(arguments, 1);
    return $opal.hash.apply(null, objs);
  });

  $defs(this, 'm$allocate', function(
    $yield) {return new $opal.hash();
  });

  $defs(this, 'm$new', function($yield, defaults) {var $block_given = ($yield != null); var block = $yield || ($yield = $no_proc, nil);var $context = $yield.$S;if (defaults === undefined) { defaults = undefined; }
    
      var hash = new $opal.hash();

      if (defaults !== undefined) {
        hash.none = defaults;
      }
      else if (block !== nil) {
        hash.proc = block;
      }

      return hash;
    
  });

  $proto.m$eq$ = function($yield, other) {var _a; 

    
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

        if (((_a = (obj).m$eq$(null, obj2)) === false || _a === nil)) {
          return false;
        }
      }

      return true;
    };

  $proto.m$aref$ = function($yield, key) {

    
      var hash = key.m$hash(),
          bucket;

      if (bucket = this.map[hash]) {
        return bucket[1];
      }

      return this.none;
    };

  $proto.m$aset$ = function($yield, key, value) {

    
      var hash       = key.m$hash();
      this.map[hash] = [key, value];

      return value;
    };

  $proto.m$assoc = function($yield, object) {

    
      for (var assoc in this.map) {
        var bucket = this.map[assoc];

        if ((bucket[0]).m$eq$(null, object)) {
          return [bucket[0], bucket[1]];
        }
      }

      return nil;
    };

  $proto.m$clear = function($yield) {

    
      this.map = {};

      return this;
    };

  $proto.m$clone = function($yield) {

    
      var result = new $opal.hash(),
          map    = this.map,
          map2   = result.map;

      for (var assoc in map) {
        map2[assoc] = [map[assoc][0], map[assoc][1]];
      }

      return result;
    };

  $proto.m$default = function($yield) {

    return this.none;};

  $proto.m$default$e = function($yield, object) {

    return this.none = object;};

  $proto.m$default_proc = function($yield) {

    return this.proc;};

  $proto.m$default_proc$e = function($yield, proc) {

    return this.proc = proc;};

  $proto.m$delete = function($yield, key) {

    
      var map  = this.map,
          hash = key.m$hash(),
          result;

      if (result = map[hash]) {
        result = bucket[1];

        delete map[hash];
      }

      return result;
    };

  $proto.m$delete_if = function($yield) {var $block_given = ($yield != null); var block = $yield || ($yield = $no_proc, nil);var $context = $yield.$S;


    if ($block_given) {} else {return this.m$enum_for(null, "delete_if")};
      var map = this.map;

      for (var assoc in map) {
        var bucket = map[assoc],
            value;

        if ((value = $yield.call($context, null, bucket[0], bucket[1])) === $breaker) {
          return $breaker.$v;
        }

        if (value !== false && value !== nil) {
          delete map[assoc];
        }
      }

      return this;
    
  };

  $proto.m$each = function($yield) {var $block_given = ($yield != null); var block = $yield || ($yield = $no_proc, nil);var $context = $yield.$S;


    if ($block_given) {} else {return this.m$enum_for(null, "each")};
      var map = this.map;

      for (var assoc in map) {
        var bucket = map[assoc];

        if ($yield.call($context, null, bucket[0], bucket[1]) === $breaker) {
          return $breaker.$v;
        }
      }

      return this;
    
  };

  $proto.m$each_key = function($yield) {var $block_given = ($yield != null); var block = $yield || ($yield = $no_proc, nil);var $context = $yield.$S;


    if ($block_given) {} else {return this.m$enum_for(null, "each_key")};
      var map = this.map;

      for (var assoc in map) {
        var bucket = map[assoc];

        if ($yield.call($context, null, bucket[0]) === $breaker) {
          return $breaker.$v;
        }
      }

      return this;
    
  };

  this.m$alias_method(null, "each_pair", "each");

  $proto.m$each_value = function($yield) {var $block_given = ($yield != null); var block = $yield || ($yield = $no_proc, nil);var $context = $yield.$S;


    if ($block_given) {} else {return this.m$enum_for(null, "each_value")};
      var map = this.map;

      for (var assoc in map) {
        var bucket = map[assoc];

        if ($yield.call($context, null, bucket[1]) === $breaker) {
          return $breaker.$v;
        }
      }

      return this;
    
  };

  $proto.m$empty$p = function($yield) {

    
      for (var assoc in this.map) {
        return false;
      }

      return true;
    };

  this.m$alias_method(null, "eql?", "==");

  $proto.m$fetch = function($yield, key, defaults) {var $block_given = ($yield != null); var block = $yield || ($yield = $no_proc, nil);var $context = $yield.$S;if (defaults === undefined) { defaults = undefined; }

    
      var bucket = this.map[key.m$hash()];

      if (block !== nil) {
        var value;

        if ((value = $yield.call($context, null, key)) === $breaker) {
          return $breaker.$v;
        }

        return value;
      }

      if (defaults !== undefined) {
        return defaults;
      }

      raise(RubyKeyError, 'key not found');
    };

  $proto.m$flatten = function($yield, level) {var _a, _b; if (level === undefined) { level = undefined; }

    
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
            result = result.concat(this.m$value().m$flatten(null, (_a = level, _b = 1, typeof(_a) === 'number' ? _a - _b : _a.m$minus$(null, _b))));
          }
        }
        else {
          result.push(value);
        }
      }

      return result;
    };

  $proto.m$has_key$p = function($yield, key) {

    return !!this.map[key.m$hash()];};

  $proto.m$has_value$p = function($yield, value) {

    
      for (var assoc in this.map) {
        if ((this.map[assoc][1]).m$eq$(null, value)) {
          return true;
        }
      }

      return false;
    };

  $proto.m$hash = function($yield) {

    return this.$id;};

  $proto.m$inspect = function($yield) {

    
      var inspect = [],
          map     = this.map;

      for (var assoc in map) {
        var bucket = map[assoc];

        inspect.push((bucket[0]).m$inspect() + '=>' + (bucket[1]).m$inspect());
      }
      return '{' + inspect.join(', ') + '}';
    };

  $proto.m$invert = function($yield) {

    
      var result = $opal.hash(),
          map    = this.map,
          map2   = result.map;

      for (var assoc in map) {
        var bucket = map[assoc];

        map2[(bucket[1]).m$hash()] = [bucket[0], bucket[1]];
      }

      return result;
    };

  $proto.m$key = function($yield, object) {

    
      for (var assoc in this.map) {
        var bucket = this.map[assoc];

        if (object.m$eq$(null, bucket[1])) {
          return bucket[0];
        }
      }

      return nil;
    };

  this.m$alias_method(null, "key?", "has_key?");

  $proto.m$keys = function($yield) {

    
      var result = [];

      for (var assoc in this.map) {
        result.push(this.map[assoc][0]);
      }

      return result;
    };

  $proto.m$length = function($yield) {

    
      var result = 0;

      for (var assoc in this.map) {
        result++;
      }

      return result;
    };

  this.m$alias_method(null, "member?", "has_key?");

  $proto.m$merge = function($yield, other) {

    
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

  $proto.m$merge$b = function($yield, other) {

    
      var map  = this.map,
          map2 = other.map;

      for (var assoc in map2) {
        var bucket = map2[assoc];

        map[assoc] = [bucket[0], bucket[1]];
      }

      return this;
    };

  $proto.m$rassoc = function($yield, object) {

    
      var map = this.map;

      for (var assoc in map) {
        var bucket = map[assoc];

        if ((bucket[1]).m$eq$(null, object)) {
          return [bucket[0], bucket[1]];
        }
      }

      return nil;
    };

  $proto.m$replace = function($yield, other) {

    
      var map = this.map = {};

      for (var assoc in other.map) {
        var bucket = other.map[assoc];

        map[assoc] = [bucket[0], bucket[1]];
      }

      return this;
    };

  this.m$alias_method(null, "size", "length");

  $proto.m$to_a = function($yield) {

    
      var map    = this.map,
          result = [];

      for (var assoc in map) {
        var bucket = map[assoc];

        result.push([bucket[0], bucket[1]]);
      }

      return result;
    };

  $proto.m$to_hash = function($yield) {

    return this;};

  $proto.m$to_native = function($yield) {var _a, _b; 

    
      var map    = this.map,
          result = {};

      for (var assoc in map) {
        var key   = map[assoc][0],
            value = map[assoc][1];

        result[key] = (function() { if ((_a = (!!(_b = value, _b != null && _b.$klass))) !== false && _a !== nil) {return (value).m$to_native()} else {return value;}; return nil; }).call(this);
      }

      return result;
    };

  this.m$alias_method(null, "to_s", "inspect");

  this.m$alias_method(null, "update", "merge!");

  return $proto.m$values = function($yield) {

    
      var map    = this.map,
          result = [];

      for (var assoc in map) {
        result.push(map[assoc][1]);
      }

      return result;
    };
}, 0);

$klass(this, nil, "String", function() {var $const = this.$const, $proto = this.$proto; 
  $defs(this, 'm$new', function($yield, str) {if (str === undefined) { str = ""; }
    return str.m$to_s()
  });

  $proto.m$lt$ = function($yield, other) {

    return this < other;};

  $proto.m$le$ = function($yield, other) {

    return this <= other;};

  $proto.m$gt$ = function($yield, other) {

    return this > other;};

  $proto.m$ge$ = function($yield, other) {

    return this >= other;};

  $proto.m$plus$ = function($yield, other) {

    return this + other;};

  $proto.m$aref$ = function($yield, index, length) {

    return this.substr(index, length);};

  $proto.m$eq$ = function($yield, other) {

    return this.valueOf() === other.valueOf();};

  $proto.m$match$ = function($yield, other) {

    
      if (typeof other === 'string') {
        raise(RubyTypeError, 'string given');
      }

      return other.m$match$(null, this);
    };

  $proto.m$cmp$ = function($yield, other) {

    
      if (typeof other !== 'string') {
        return nil;
      }

      return this > other ? 1 : (this < other ? -1 : 0);
    };

  $proto.m$capitalize = function($yield) {

    return this.charAt(0).toUpperCase() + this.substr(1).toLowerCase();};

  $proto.m$casecmp = function($yield, other) {

    
      if (typeof other !== 'string') {
        return other;
      }

      var a = this.toLowerCase(),
          b = other.toLowerCase();

      return a > b ? 1 : (a < b ? -1 : 0);
    };

  $proto.m$downcase = function($yield) {

    return this.toLowerCase();};

  $proto.m$end_with$p = function($yield, suffix) {

    return this.lastIndexOf(suffix) === this.length - suffix.length;};

  $proto.m$empty$p = function($yield) {

    return this.length === 0;};

  $proto.m$gsub = function($yield, pattern, replace) {var _a, _b; var $block_given = ($yield != null); var block = $yield || ($yield = $no_proc, nil);var $context = $yield.$S;if (replace === undefined) { replace = undefined; }

    
      var re = pattern.toString();
          re = re.substr(1, re.lastIndexOf('/') - 1);
          re = new RegExp(re, 'g');

      return this.m$sub((_b = block, (typeof(_b) === 'function' || _b == nil ? _b : _b.m$to_proc())), this.m$re(), replace);
    };

  $proto.m$hash = function($yield) {

    return this.toString();};

  $proto.m$include$p = function($yield, other) {

    return this.indexOf(other) !== -1;};

  $proto.m$index = function($yield, substr) {

    
      var result = this.indexOf(substr);
      return result === -1 ? nil : result
    };

  $proto.m$inspect = function($yield) {

    return string_inspect(this);};

  $proto.m$intern = function($yield) {

    return this;};

  $proto.m$length = function($yield) {

    return this.length;};

  $proto.m$lstrip = function($yield) {

    return this.replace(/^s*/, '');};

  $proto.m$next = function($yield) {

    return String.fromCharCode(this.charCodeAt(0));};

  $proto.m$reverse = function($yield) {

    return this.split('').reverse().join('');};

  $proto.m$split = function($yield, split, limit) {if (limit === undefined) { limit = undefined; }

    return this.split(split, limit);};

  $proto.m$start_with$p = function($yield, prefix) {

    return this.indexOf(prefix) === 0;};

  $proto.m$sub = function($yield, pattern, replace) {var $block_given = ($yield != null); var block = $yield || ($yield = $no_proc, nil);var $context = $yield.$S;if (replace === undefined) { replace = undefined; }

    
      if (block !== nil) {
        return this.replace(pattern, function(str) {
          return $yield.call($context, null, str);
        });
      }
      else {
        return this.replace(pattern, replace);
      }
    };

  this.m$alias_method(null, "succ", "next");

  $proto.m$to_f = function($yield) {

    return parseFloat(this);};

  $proto.m$to_i = function($yield, base) {if (base === undefined) { base = 10; }

    return parseInt(this, base);};

  $proto.m$to_native = function($yield) {

    return this.valueOf();};

  $proto.m$to_proc = function($yield) {

    
      var self = this;
      return function(iter, arg) { return arg['m$' + self](); };
    };

  $proto.m$to_s = function($yield) {

    return this.toString();};

  this.m$alias_method(null, "to_sym", "intern");

  return $proto.m$upcase = function($yield) {

    return this.toUpperCase();};
}, 0);

$const.Symbol = 

$const.String;$klass(this, nil, "Numeric", function() {var $const = this.$const, $proto = this.$proto; 
  $proto.m$plus$ = function($yield, other) {

    return this + other;};

  $proto.m$minus$ = function($yield, other) {

    return this - other;};

  $proto.m$mul$ = function($yield, other) {

    return this * other;};

  $proto.m$div$ = function($yield, other) {

    return this / other;};

  $proto.m$mod$ = function($yield, other) {

    return this % other;};

  $proto.m$and$ = function($yield, other) {

    return this & other;};

  $proto.m$or$ = function($yield, other) {

    return this | other;};

  $proto.m$xor$ = function($yield, other) {

    return this ^ other;};

  $proto.m$lt$ = function($yield, other) {

    return this < other;};

  $proto.m$le$ = function($yield, other) {

    return this <= other;};

  $proto.m$gt$ = function($yield, other) {

    return this > other;};

  $proto.m$ge$ = function($yield, other) {

    return this >= other;};

  $proto.m$lshft$ = function($yield, count) {

    return this << count;};

  $proto.m$rshft$ = function($yield, count) {

    return this >> count;};

  $proto.m$uplus$ = function($yield) {

    return +this;};

  $proto.m$uminus$ = function($yield) {

    return -this;};

  $proto.m$tild$ = function($yield) {

    return ~this;};

  $proto.m$pow$ = function($yield, other) {

    return Math.pow(this, other);};

  $proto.m$eq$ = function($yield, other) {

    return this.valueOf() === other.valueOf();};

  $proto.m$cmp$ = function($yield, other) {var _a, _b; 

    
      if (((_a = (typeof other === 'number')) === false || _a === nil)) {
        return nil;
      }

      return this < other ? -1 : (this > other ? 1 : 0);
    };

  $proto.m$abs = function($yield) {

    return Math.abs(this);};

  $proto.m$ceil = function($yield) {

    return Math.ceil(this);};

  $proto.m$downto = function($yield, finish) {var $block_given = ($yield != null); var block = $yield || ($yield = $no_proc, nil);var $context = $yield.$S;


    if ($block_given) {} else {return this.m$enum_for(null, "downto", finish)};
      for (var i = this; i >= finish; i--) {
        if ($yield.call($context, null, i) === $breaker) {
          return $breaker.$v;
        }
      }

      return this;
    
  };

  $proto.m$even$p = function($yield) {

    return this % 2 === 0;};

  $proto.m$floor = function($yield) {

    return Math.floor(this);};

  $proto.m$hash = function($yield) {

    return this.toString();};

  $proto.m$integer$p = function($yield) {

    return this % 1 === 0;};

  this.m$alias_method(null, "magnitude", "abs");

  this.m$alias_method(null, "modulo", "%");

  $proto.m$next = function($yield) {

    return this + 1;};

  $proto.m$nonzero$p = function($yield) {

    return this.valueOf() === 0 ? nil : this;};

  $proto.m$odd$p = function($yield) {

    return this % 2 !== 0;};

  $proto.m$pred = function($yield) {

    return this - 1;};

  this.m$alias_method(null, "succ", "next");

  $proto.m$times = function($yield) {var _a; var $block_given = ($yield != null); var block = $yield || ($yield = $no_proc, nil);var $context = $yield.$S;


    if ((_a = block) !== false && _a !== nil) {} else {return this.m$enum_for(null, "times")};
      for (var i = 0; i <= this; i++) {
        if ($yield.call($context, null, i) === $breaker) {
          return $breaker.$v;
        }
      }

      return this;
    
  };

  $proto.m$to_f = function($yield) {

    return parseFloat(this);};

  $proto.m$to_i = function($yield) {

    return parseInt(this);};

  $proto.m$to_native = function($yield) {

    return this.valueOf();};

  $proto.m$to_s = function($yield, base) {if (base === undefined) { base = 10; }

    return this.toString(base);};

  $proto.m$upto = function($yield, finish) {var $block_given = ($yield != null); var block = $yield || ($yield = $no_proc, nil);var $context = $yield.$S;


    if ($block_given) {} else {return this.m$enum_for(null, "upto", finish)};
      for (var i = 0; i <= finish; i++) {
        if ($yield.call($context, null, i) === $breaker) {
          return $breaker.$v;
        }
      }

      return this;
    
  };

  return $proto.m$zero$p = function($yield) {

    return this.valueOf() === 0;};
}, 0);

$klass(this, nil, "Integer", function() {var $const = this.$const, $proto = this.$proto; 
  return $defs(this, 'm$eqq$', function($yield, obj) {var _a, _b; 
    
      if (((_a = (typeof obj === 'number')) === false || _a === nil)) {
        return false;
      }

      return other % 1 === 0;
    
  })
}, 0);

$klass(this, nil, "Float", function() {var $const = this.$const, $proto = this.$proto; 
  return $defs(this, 'm$eqq$', function($yield, obj) {var _a, _b; 
    
      if (((_a = (typeof obj === 'number')) === false || _a === nil)) {
        return false;
      }

      return obj % 1 !== 0;
    
  })
}, 0);

$klass(this, nil, "Rational", function() {var $const = this.$const, $proto = this.$proto; 
  this.m$attr_reader(null, "numerator", "denominator");

  $proto.m$initialize = function($yield, numerator, denominator) {if (denominator === undefined) { denominator = 1; }
    this.numerator = 
    numerator;return this.denominator = 
    denominator;};

  $proto.m$to_s = function($yield) {var _a; 

    return ("" + this.m$numerator().m$to_s() + (function() { if ((_a = this.m$denominator()) !== false && _a !== nil) {return ("/" + this.m$denominator().m$to_s())} else {return nil}; return nil; }).call(this).m$to_s());};

  return $proto.m$inspect = function($yield) {

    return ("(" + this.m$to_s().m$to_s() + ")");};
}, 0);

$klass(this, nil, "Complex", function() {var $const = this.$const, $proto = this.$proto; 
  return nil}, 0);

$klass(this, nil, "Proc", function() {var $const = this.$const, $proto = this.$proto; 
  $defs(this, 'm$new', function($yield) {var $block_given = ($yield != null); var block = $yield || ($yield = $no_proc, nil);var $context = $yield.$S;


    if ($block_given) {} else {this.m$raise(null, $const.ArgumentError, "tried to create Proc object without a block")};
    return block;});

  $proto.m$to_proc = function($yield) {

    return this;};

  $proto.m$call = function($yield, args) {args = $slice.call(arguments, 1);

    return this.apply(this.$S, $slice.call(arguments));};

  $proto.m$to_native = function($yield) {

    
      return function() {
        var args = Array.slice.call(arguments);
            args.unshift(null); // block

        return this.apply(this.$S, args);
      };
    };

  $proto.m$to_proc = function($yield) {

    return this;};

  $proto.m$to_s = function($yield) {

    return "#<Proc:0x0000000>";};

  $proto.m$lambda$p = function($yield) {

    return this.$lambda ? true : false;};

  return $proto.m$arity = function($yield) {

    return this.length - 1;};
}, 0);

$klass(this, nil, "Range", function() {var $const = this.$const, $proto = this.$proto; 
  $proto.m$begin = function($yield) {

    return this.begin;};

  $proto.m$end = function($yield) {

    return this.end;};

  this.m$alias_method(null, "first", "begin");
  this.m$alias_method(null, "min", "begin");

  this.m$alias_method(null, "last", "end");
  this.m$alias_method(null, "max", "end");

  $proto.m$initialize = function($yield, min, max, exclude) {if (exclude === undefined) { exclude = false; }
    this.begin = this.begin   = min;
    this.end = this.end     = max;
    return this.exclude = this.exclude = exclude;
  };


  $proto.m$eqq$ = function($yield, obj) {

    return obj >= this.begin && obj <= this.end;};

  $proto.m$exclude_end$p = function($yield) {

    return this.exclude;};

  $proto.m$to_s = function($yield) {

    return this.begin + (this.exclude ? '...' : '..') + this.end;};

  return $proto.m$inspect = function($yield) {

    return this.begin + (this.exclude ? '...' : '..') + this.end;};
}, 0);

$klass(this, nil, "Exception", function() {var $const = this.$const, $proto = this.$proto; 
  $proto.m$initialize = function($yield, message) {if (message === undefined) { message = ""; }

    
      if (Error.captureStackTrace) {
        Error.captureStackTrace(this);
      }

      this.message = message;
    };

  $proto.m$backtrace = function($yield) {

    return this._bt || (this._bt = exc_backtrace(this));};

  $proto.m$inspect = function($yield) {

    return ("#<" + this.m$class().m$to_s() + ": '" + this.m$message().m$to_s() + "'>");};

  $proto.m$message = function($yield) {

    return this.message;};

  return this.m$alias_method(null, "to_s", "message");
}, 0);

$klass(this, nil, "Regexp", function() {var $const = this.$const, $proto = this.$proto; 
  $defs(this, 'm$escape', function($yield, string) {
    return string.replace(/([.*+?^=!:${}()|[]\/\])/g, '\$1');
  });

  $defs(this, 'm$new', function($yield, string, options) {if (options === undefined) { options = undefined; }
    return new RegExp(string, options);
  });

  $proto.m$eq$ = function($yield, other) {

    return other.constructor == RegExp && this.toString() === other.toString();};

  $proto.m$eqq$ = function($yield, obj) {

    return this.test(obj);};

  $proto.m$match$ = function($yield, string) {

    
      var result        = this.exec(string);

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

  this.m$alias_method(null, "eql?", "==");

  $proto.m$inspect = function($yield) {

    return this.toString();};

  $proto.m$match = function($yield, pattern) {

    
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

  $proto.m$to_native = function($yield) {

    return this;};

  return $proto.m$to_s = function($yield) {

    return this.source;};
}, 0);

$klass(this, nil, "MatchData", function() {var $const = this.$const, $proto = this.$proto; 
  $proto.m$aref$ = function($yield, index) {

    
      var length = this.$data.length;

      if (index < 0) {
        index += length;
      }

      if (index >= length || index < 0) {
        return nil;
      }

      return this.$data[index];
    };

  $proto.m$length = function($yield) {

    return this.$data.length;};

  $proto.m$inspect = function($yield) {

    return ("#<MatchData " + this.m$aref$(null, 0).m$inspect().m$to_s() + ">");};

  this.m$alias_method(null, "size", "length");

  $proto.m$to_a = function($yield) {

    return [].slice.call(this.$data, 0);};

  $opal.alias(this, "to_native", "to_a");

  return $proto.m$to_s = function($yield) {

    return this.$data[0];};
}, 0);

$klass(this, nil, "Struct", function() {var $const = this.$const, $proto = this.$proto; 
  $defs(this, 'm$new', function($yield, name, args) {var _a; args = $slice.call(arguments, 2);
    if ((_a = this.m$eq$(

    null, $const.Struct)) !== false && _a !== nil) {} else {return $opal.zuper(arguments.callee, this, [])};if ((_a = name.m$is_a$p(null, $const.String)) !== false && _a !== nil) {
      return $const.Struct.m$const_set(null, name, (_a=this).m$new.apply(_a, [null].concat(args)))} else {

      args.m$unshift(

      null, name);return $const.Class.m$new((_a=function(_$) {var _a; 
        return args.m$each((_a=function(_$, name) {if (name === undefined) {name = nil; }return this.m$define_struct_attribute(null, name)},_a.$S=this,_a))
      },_a.$S=this,_a), this);
    };
  });

  $defs(this, 'm$define_struct_attribute', function($yield, name) {var _a; 
    this.m$members().m$lshft$(

    null, name);this.m$define_method((_a=function(_$) {
      return this.m$instance_variable_get(null, ("@" + name.m$to_s()))
    },_a.$S=this,_a), name);

    return this.m$define_method((_a=function(_$, value) {if (value === undefined) {value = nil; }
      return this.m$instance_variable_set(null, ("@" + name.m$to_s()), 
      value)},_a.$S=this,_a), ("" + name.m$to_s() + "="));
  });

  $defs(this, 'm$members', function(
    $yield) {var _a; this.members == null && (this.members = nil);return (_a = this.members, _a !== false && _a != nil ? _a : this.members = [])
  });



  this.m$include(null, $const.Enumerable);$proto.m$initialize = function($yield, args) {var _a; args = $slice.call(arguments, 1);



    return this.m$members().m$each_with_index((_a=function(_$, name, index) {if (name === undefined) {name = nil; }if (index === undefined) {index = nil; }return this.m$instance_variable_set(null, ("@" + name.m$to_s()), args.m$aref$(null, index))},_a.$S=this,_a));};

  $proto.m$members = function($yield) {

    return this.m$class().m$members();};

  $proto.m$aref$ = function($yield, name) {var _a, _b; 
    if ((_a = name.m$is_a$p(null, $const.Integer)) !== false && _a !== nil) {
      if ((_a = name, _b = this.m$members().m$size(), typeof(_a) === 'number' ? _a >= _b : _a.m$ge$(null, _b))) {this.m$raise(null, $const.IndexError, ("offset " + name.m$to_s() + " too large for struct(size:" + this.m$members().m$size().m$to_s() + ")"))

      };name = this.m$members().m$aref$(null, name);} else {

      if ((_b = this.m$members().m$include$p(null, name.m$to_sym())) !== false && _b !== nil) {} else {this.m$raise(null, $const.NameError, ("no member '" + name.m$to_s() + "' in struct"))
      }};

    return this.m$instance_variable_get(null, ("@" + name.m$to_s()));
  };

  $proto.m$aset$ = function($yield, name, value) {var _a, _b; 
    if ((_a = name.m$is_a$p(null, $const.Integer)) !== false && _a !== nil) {
      if ((_a = name, _b = this.m$members().m$size(), typeof(_a) === 'number' ? _a >= _b : _a.m$ge$(null, _b))) {this.m$raise(null, $const.IndexError, ("offset " + name.m$to_s() + " too large for struct(size:" + this.m$members().m$size().m$to_s() + ")"))

      };name = this.m$members().m$aref$(null, name);} else {

      if ((_b = this.m$members().m$include$p(null, name.m$to_sym())) !== false && _b !== nil) {} else {this.m$raise(null, $const.NameError, ("no member '" + name.m$to_s() + "' in struct"))
      }};

    return this.m$instance_variable_set(null, ("@" + name.m$to_s()), 
    value);};

  $proto.m$each = function($yield) {var _a; try {var $block_given = ($yield != null); $yield || ($yield = $no_proc);var $context = $yield.$S;


    if ($block_given) {} else {return this.m$enum_for(null, "each")};return this.m$members().m$each((_a=function(_$, name) {var _a; if (name === undefined) {name = nil; }return ((_a = $yield.call($context, null, this.m$aref$(null, name))) === $breaker ? _a.$t() : _a)},_a.$S=this,_a));} catch (e) { if (e === $breaker) { return e.$v; }; throw e;}
  };

  $proto.m$each_pair = function($yield) {var _a; try {var $block_given = ($yield != null); $yield || ($yield = $no_proc);var $context = $yield.$S;


    if ($block_given) {} else {return this.m$enum_for(null, "each_pair")};return this.m$members().m$each((_a=function(_$, name) {var _a; if (name === undefined) {name = nil; }return ((_a = $yield.call($context, null, name, this.m$aref$(null, name))) === $breaker ? _a.$t() : _a)},_a.$S=this,_a));} catch (e) { if (e === $breaker) { return e.$v; }; throw e;}
  };

  $proto.m$eql$p = function($yield, other) {var _a, _b; 



    return (_a = this.m$hash().m$eq$(null, other.m$hash()), _a !== false && _a != nil ? _a : other.m$each_with_index().m$all$p((_b=function(_$, object, index) {if (object === undefined) {object = nil; }if (index === undefined) {index = nil; }return this.m$aref$(null, this.m$members().m$aref$(null, index)).m$eq$(null, object)},_b.$S=this,_b)));};

  $proto.m$length = function($yield) {

    return this.m$members().m$length();};

  $opal.alias(this, "size", "length");

  $proto.m$to_a = function($yield) {var _a; 

    return this.m$members().m$map((_a=function(_$, name) {if (name === undefined) {name = nil; }return this.m$aref$(null, name)},_a.$S=this,_a));};

  return $opal.alias(this, "values", "to_a");
}, 0);

$klass(this, nil, "Time", function() {var $const = this.$const, $proto = this.$proto; 

  this.m$include(null, $const.Native);

  this.m$include(null, $const.Comparable);$defs(this, 'm$at', function($yield, seconds, frac) {if (frac === undefined) { frac = 0; }
    return this.m$from_native(null, new Date(seconds * 1000 + frac))
  });

  $defs(this, 'm$now', function(
    $yield) {return this.m$from_native(null, new Date())
  });

  $proto.m$initialize = function($yield, year, month, day, hour, min, sec, utc_offset) {var _a; if (year === undefined) { year = nil; }if (month === undefined) { month = nil; }if (day === undefined) { day = nil; }if (hour === undefined) { hour = nil; }if (min === undefined) { min = nil; }if (sec === undefined) { sec = nil; }if (utc_offset === undefined) { utc_offset = nil; }





    if ((_a = year) !== false && _a !== nil) {return $opal.zuper(arguments.callee, this, [new Date(year.m$to_native(), month.m$to_native(), day.m$to_native(), hour.m$to_native(), min.m$to_native(), sec.m$to_native())])} else {return $opal.zuper(arguments.callee, this, [new Date()])};};

  $proto.m$plus$ = function($yield, other) {var _a, _b; 

    return this.m$from_native(null, new Date((_a = this.m$to_f(), _b = other.m$to_f(), typeof(_a) === 'number' ? _a + _b : _a.m$plus$(null, _b))));};

  $proto.m$minus$ = function($yield, other) {var _a, _b; 

    return this.m$from_native(null, new Date((_a = this.m$to_f(), _b = other.m$to_f(), typeof(_a) === 'number' ? _a - _b : _a.m$minus$(null, _b))));};

  $proto.m$cmp$ = function($yield, other) {

    return this.m$to_f().m$cmp$(null, other.m$to_f());};

  $proto.m$asctime = function($yield) {

    return this.m$raise(null, $const.NotImplementedError);};

  $opal.alias(this, "ctime", "asctime");

  $proto.m$day = function($yield) {this['native'] == null && (this['native'] = nil);

    return this['native'].getDate();};

  $proto.m$dst$p = function($yield) {

    return this.m$raise(null, $const.NotImplementedError);};

  $proto.m$eql$p = function($yield, other) {var _a; 

    return (_a = other.m$is_a$p(null, $const.Time), _a !== false && _a != nil ? this.m$cmp$(null, other).m$zero$p() : _a);};

  $proto.m$friday$p = function($yield) {

    return this.m$wday().m$eq$(null, 5);};

  $proto.m$getgm = function($yield) {

    return this.m$raise(null, $const.NotImplementedError);};

  $proto.m$getlocal = function($yield) {

    return this.m$raise(null, $const.NotImplementedError);};

  $opal.alias(this, "getutc", "getgm");

  $proto.m$gmt$p = function($yield) {

    return this.m$raise(null, $const.NotImplementedError);};

  $proto.m$gmt_offset = function($yield) {

    return this.m$raise(null, $const.NotImplementedError);};

  $proto.m$gmtime = function($yield) {

    return this.m$raise(null, $const.NotImplementedError);};

  $opal.alias(this, "gmtoff", "gmt_offset");

  $proto.m$hour = function($yield) {this['native'] == null && (this['native'] = nil);

    return this['native'].getHours();};

  $opal.alias(this, "isdst", "dst?");

  $proto.m$localtime = function($yield) {

    return this.m$raise(null, $const.NotImplementedError);};

  $opal.alias(this, "mday", "day");

  $proto.m$min = function($yield) {this['native'] == null && (this['native'] = nil);

    return this['native'].getMinutes();};

  $proto.m$mon = function($yield) {this['native'] == null && (this['native'] = nil);

    return this['native'].getMonth() + 1;};

  $proto.m$monday$p = function($yield) {

    return this.m$wday().m$eq$(null, 1);};

  $opal.alias(this, "month", "mon");

  $proto.m$nsec = function($yield) {

    return this.m$raise(null, $const.NotImplementedError);};

  $proto.m$round = function($yield) {

    return this.m$raise(null, $const.NotImplementedError);};

  $proto.m$saturday$p = function($yield) {

    return this.m$wday().m$eq$(null, 6);};

  $proto.m$sec = function($yield) {this['native'] == null && (this['native'] = nil);

    return this['native'].getSeconds();};

  $proto.m$strftime = function($yield, string) {

    return this.m$raise(null, $const.NotImplementedError);};

  $proto.m$subsec = function($yield) {

    return this.m$raise(null, $const.NotImplementedError);};

  $proto.m$sunday$p = function($yield) {

    return this.m$wday().m$eq$(null, 0);};

  $proto.m$thursday$p = function($yield) {

    return this.m$wday().m$eq$(null, 4);};

  $proto.m$to_a = function($yield) {

    return this.m$raise(null, $const.NotImplementedError);};

  $proto.m$to_f = function($yield) {this['native'] == null && (this['native'] = nil);

    return this['native'].getTime() / 1000;};

  $proto.m$to_i = function($yield) {this['native'] == null && (this['native'] = nil);

    return parseInt(this['native'].getTime() / 1000);};

  $proto.m$to_r = function($yield) {

    return this.m$raise(null, $const.NotImplementedError);};

  $proto.m$to_s = function($yield) {

    return this.m$raise(null, $const.NotImplementedError);};

  $proto.m$tuesday$p = function($yield) {

    return this.m$wday().m$eq$(null, 2);};

  $opal.alias(this, "tv_nsec", "nsec");

  $opal.alias(this, "tv_sec", "to_i");

  $proto.m$tv_usec = function($yield) {

    return this.m$raise(null, $const.NotImplementedError);};

  $opal.alias(this, "usec", "tv_usec");

  $opal.alias(this, "utc", "gmtime");

  $opal.alias(this, "utc?", "gmt?");

  $opal.alias(this, "utc_offset", "gmt_offset");

  $proto.m$wday = function($yield) {this['native'] == null && (this['native'] = nil);

    return this['native'].getDay();};

  $proto.m$wednesday$p = function($yield) {

    return this.m$wday().m$eq$(null, 3);};

  $proto.m$yday = function($yield) {

    return this.m$raise(null, $const.NotImplementedError);};

  $proto.m$year = function($yield) {this['native'] == null && (this['native'] = nil);

    return this['native'].getFullYear();};

  return $proto.m$zone = function($yield) {

    return this.m$raise(null, $const.NotImplementedError);};
}, 0);

$klass(this, nil, "IO", function() {var $const = this.$const, $proto = this.$proto; 
  $proto.m$puts = function($yield, args) {var _a; args = $slice.call(arguments, 1);
    if ((_a = args.m$empty$p()) !== false && _a !== nil) {return this.m$flush()

    };return args.m$each((_a=function(_$, a) {if (a === undefined) {a = nil; }
      this.m$write(null, a.m$to_s());

      return this.m$flush();},_a.$S=this,_a));
  };

  $proto.m$print = function($yield, args) {var _a; args = $slice.call(arguments, 1);
    args.m$each((_a=function(_$, a) {if (a === undefined) {a = nil; }return this.m$write(null, a.m$to_s())},_a.$S=this,_a));

    return nil;
  };

  $proto.m$write = function($yield) {

    return nil;};

  return $proto.m$flush = function($yield) {

    return this;};
}, 0);

$const.STDOUT = ($opal.gvars["$stdout"] = $const.IO.m$new());

$klass(((_a = $opal.gvars["$stdout"]) == null ? nil : _a), nil, nil, function() {var $const = this.$const; 

var stdout_buffer = [];

$defn(this, 'm$write', function($yield, str) {
  stdout_buffer.push(str);

  return nil;
});

return $defn(this, 'm$flush', function($yield) {
  console.log(stdout_buffer.join(''));
  stdout_buffer = [];

  return nil;
});}, 2);


$klass(this, nil, "File", function() {var $const = this.$const, $proto = this.$proto; 
  $defs(this, 'm$expand_path', function($yield, path, base) {if (base === undefined) { base = undefined; }
    
      if (!base) {
        if (path.charAt(0) !== '/') {
          base = FS_CWD;
        }
        else {
          base = '';
        }
      }

      path = this.m$join(null, base, path);

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

  $defs(this, 'm$join', function($yield, paths) {paths = $slice.call(arguments, 1);
    return paths.join('/');
  });

  $defs(this, 'm$dirname', function($yield, path) {
    
      var dirname = PATH_RE.exec(path)[1];

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

  $defs(this, 'm$extname', function($yield, path) {
    
      var extname = PATH_RE.exec(path)[3];

      if (!extname || extname === '.') {
        return '';
      }
      else {
        return extname;
      }
    
  });

  $defs(this, 'm$basename', function($yield, path, suffix) {
    return $opal.fs.basename(path, suffix);
  });

  return $defs(this, 'm$exist$p', function($yield, path) {
    return opal.loader.factories[this.m$expand_path(null, path)] ? true : false;
  });
}, 0);

return $klass(this, nil, "Dir", function() {var $const = this.$const, $proto = this.$proto; 
  $defs(this, 'm$getwd', function(
    $yield) {return FS_CWD;
  });

  $defs(this, 'm$pwd', function(
    $yield) {return FS_CWD;
  });

  return $defs(this, 'm$aref$', function($yield, globs) {globs = $slice.call(arguments, 1);
    
      var result = [], files = FACTORIES;

      for (var i = 0, ii = globs.length; i < ii; i++) {
        var glob = globs[i];

        var re = fs_glob_to_regexp($const.File.m$expand_path(null, glob));

        for (var file in files) {
          if (re.exec(file)) {
            result.push(file);
          }
        }
      }

      return result;
    
  });
}, 0);
}).call(opal.top, opal);
}).call(this);