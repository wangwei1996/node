// Copyright Joyent, Inc. and other Node contributors.
//
// Permission is hereby granted, free of charge, to any person obtaining a
// copy of this software and associated documentation files (the
// "Software"), to deal in the Software without restriction, including
// without limitation the rights to use, copy, modify, merge, publish,
// distribute, sublicense, and/or sell copies of the Software, and to permit
// persons to whom the Software is furnished to do so, subject to the
// following conditions:
//
// The above copyright notice and this permission notice shall be included
// in all copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
// OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
// MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN
// NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
// DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR
// OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE
// USE OR OTHER DEALINGS IN THE SOFTWARE.

'use strict';

const {
  JSON,
  Object,
  ObjectPrototype,
  Reflect,
  SafeMap,
  StringPrototype,
} = primordials;

const { NativeModule } = require('internal/bootstrap/loaders');
const {
  maybeCacheSourceMap,
  rekeySourceMap
} = require('internal/source_map/source_map_cache');
const { pathToFileURL, fileURLToPath, URL } = require('internal/url');
const { deprecate } = require('internal/util');
const vm = require('vm');
const assert = require('internal/assert');
const fs = require('fs');
const internalFS = require('internal/fs/utils');
const path = require('path');
const {
  internalModuleReadJSON,
  internalModuleStat
} = internalBinding('fs');
const { safeGetenv } = internalBinding('credentials');
const {
  makeRequireFunction,
  normalizeReferrerURL,
  stripBOM,
  stripShebang,
  loadNativeModule
} = require('internal/modules/cjs/helpers');
const { getOptionValue } = require('internal/options');
const enableSourceMaps = getOptionValue('--enable-source-maps');
const preserveSymlinks = getOptionValue('--preserve-symlinks');
const preserveSymlinksMain = getOptionValue('--preserve-symlinks-main');
const experimentalModules = getOptionValue('--experimental-modules');
const manifest = getOptionValue('--experimental-policy') ?
  require('internal/process/policy').manifest :
  null;
const { compileFunction } = internalBinding('contextify');

const {
  ERR_INVALID_ARG_VALUE,
  ERR_INVALID_OPT_VALUE,
  ERR_REQUIRE_ESM
} = require('internal/errors').codes;
const { validateString } = require('internal/validators');
const pendingDeprecation = getOptionValue('--pending-deprecation');
const experimentalExports = getOptionValue('--experimental-exports');

module.exports = Module;

let asyncESM, ModuleJob, ModuleWrap, kInstantiated;

const {
  CHAR_FORWARD_SLASH,
  CHAR_BACKWARD_SLASH,
  CHAR_COLON
} = require('internal/constants');

const isWindows = process.platform === 'win32';

const relativeResolveCache = Object.create(null);

let requireDepth = 0;
let statCache = null;

function enrichCJSError(err) {
  const stack = err.stack.split('\n');

  const lineWithErr = stack[1];

  /*
    The regular expression below targets the most common import statement
    usage. However, some cases are not matching, cases like import statement
    after a comment block and/or after a variable definition.
  */
  if (err.message.startsWith('Unexpected token \'export\'') ||
    (/^\s*import(?=[ {'"*])\s*(?![ (])/).test(lineWithErr)) {
    process.emitWarning(
      'To load an ES module, set "type": "module" in the package.json or use ' +
      'the .mjs extension.',
      undefined,
      undefined,
      undefined,
      true);
  }
}

/**
 * 调用internalModuleStat方法来判断文件或者文件夹是否存在，文件存在返回0，文件夹存在返回1，文件或文件夹不存在返回-2
 * @param {*} filename 
 */
function stat(filename) {
  // 仅在 Windows 系统上，返回给定 path 的等效名称空间前缀路径
  filename = path.toNamespacedPath(filename);
  if (statCache !== null) {
    const result = statCache.get(filename);
    if (result !== undefined) return result;
  }
  const result = internalModuleStat(filename);
  if (statCache !== null) statCache.set(filename, result);
  return result;
}

function updateChildren(parent, child, scan) {
  const children = parent && parent.children;
  if (children && !(scan && children.includes(child)))
    children.push(child);
}

function Module(id = '', parent) {
  this.id = id;
  this.path = path.dirname(id);
  this.exports = {};
  this.parent = parent;
  updateChildren(parent, this, false);
  this.filename = null;
  this.loaded = false;
  this.children = [];
}

const builtinModules = [];
for (const [id, mod] of NativeModule.map) {
  if (mod.canBeRequiredByUsers) {
    builtinModules.push(id);
  }
}

Object.freeze(builtinModules);
Module.builtinModules = builtinModules;

Module._cache = Object.create(null);
Module._pathCache = Object.create(null);
Module._extensions = Object.create(null);
let modulePaths = [];
Module.globalPaths = [];

let patched = false;

// eslint-disable-next-line func-style
let wrap = function(script) {
  return Module.wrapper[0] + script + Module.wrapper[1];
};

const wrapper = [
  '(function (exports, require, module, __filename, __dirname) { ',
  '\n});'
];

let wrapperProxy = new Proxy(wrapper, {
  set(target, property, value, receiver) {
    patched = true;
    return Reflect.set(target, property, value, receiver);
  },

  defineProperty(target, property, descriptor) {
    patched = true;
    return Object.defineProperty(target, property, descriptor);
  }
});

Object.defineProperty(Module, 'wrap', {
  get() {
    return wrap;
  },

  set(value) {
    patched = true;
    wrap = value;
  }
});

Object.defineProperty(Module, 'wrapper', {
  get() {
    return wrapperProxy;
  },

  set(value) {
    patched = true;
    wrapperProxy = value;
  }
});

const debug = require('internal/util/debuglog').debuglog('module');
Module._debug = deprecate(debug, 'Module._debug is deprecated.', 'DEP0077');

// Given a module name, and a list of paths to test, returns the first
// matching file in the following precedence.
//
// require("a.<ext>")
//   -> a.<ext>
//
// require("a")
//   -> a
//   -> a.<ext>
//   -> a/index.<ext>

const packageJsonCache = new SafeMap();

function readPackage(requestPath) {
  const jsonPath = path.resolve(requestPath, 'package.json');

  const existing = packageJsonCache.get(jsonPath);
  if (existing !== undefined) return existing;

  const json = internalModuleReadJSON(path.toNamespacedPath(jsonPath));
  if (json === undefined) {
    packageJsonCache.set(jsonPath, false);
    return false;
  }

  if (manifest) {
    const jsonURL = pathToFileURL(jsonPath);
    manifest.assertIntegrity(jsonURL, json);
  }

  try {
    const parsed = JSON.parse(json);
    const filtered = {
      main: parsed.main,
      exports: parsed.exports,
      type: parsed.type
    };
    packageJsonCache.set(jsonPath, filtered);
    return filtered;
  } catch (e) {
    e.path = jsonPath;
    e.message = 'Error parsing ' + jsonPath + ': ' + e.message;
    throw e;
  }
}

function readPackageScope(checkPath) {
  const rootSeparatorIndex = checkPath.indexOf(path.sep);
  let separatorIndex;
  while (
    (separatorIndex = checkPath.lastIndexOf(path.sep)) > rootSeparatorIndex
  ) {
    checkPath = checkPath.slice(0, separatorIndex);
    if (checkPath.endsWith(path.sep + 'node_modules'))
      return false;
    const pjson = readPackage(checkPath);
    if (pjson) return {
      path: checkPath,
      data: pjson
    };
  }
  return false;
}

function readPackageMain(requestPath) {
  const pkg = readPackage(requestPath);
  return pkg ? pkg.main : undefined;
}

function readPackageExports(requestPath) {
  const pkg = readPackage(requestPath);
  return pkg ? pkg.exports : undefined;
}


/**
 * 先尝试加载该目录下的 package.json 中 main 入口指定的文件
   如果不存在，然后尝试 index[.js, .node, .json] 文件
 * @param {*} requestPath 文件绝对路径
 * @param {*} exts  允许的文件后缀名
 * @param {*} isMain  是否为主程序
 * @param {*} originalPath  require函数的入参
 */
function tryPackage(requestPath, exts, isMain, originalPath) {
  const pkg = readPackageMain(requestPath);

  if (!pkg) {
    return tryExtensions(path.resolve(requestPath, 'index'), exts, isMain);
  }

  const filename = path.resolve(requestPath, pkg);
  let actual = tryFile(filename, isMain) ||
    tryExtensions(filename, exts, isMain) ||
    tryExtensions(path.resolve(filename, 'index'), exts, isMain);
  if (actual === false) {
    actual = tryExtensions(path.resolve(requestPath, 'index'), exts, isMain);
    if (!actual) {
      // eslint-disable-next-line no-restricted-syntax
      const err = new Error(
        `Cannot find module '${filename}'. ` +
        'Please verify that the package.json has a valid "main" entry'
      );
      err.code = 'MODULE_NOT_FOUND';
      err.path = path.resolve(requestPath, 'package.json');
      err.requestPath = originalPath;
      // TODO(BridgeAR): Add the requireStack as well.
      throw err;
    } else if (pendingDeprecation) {
      const jsonPath = path.resolve(requestPath, 'package.json');
      process.emitWarning(
        `Invalid 'main' field in '${jsonPath}' of '${pkg}'. ` +
          'Please either fix that or report it to the module author',
        'DeprecationWarning',
        'DEP0128'
      );
    }
  }
  return actual;
}

// In order to minimize unnecessary lstat() calls,
// this cache is a list of known-real paths.
// Set to an empty Map to reset.
const realpathCache = new Map();

// Check if the file exists and is not a directory
// if using --preserve-symlinks and isMain is false,
// keep symlinks intact, otherwise resolve to the
// absolute realpath.
function tryFile(requestPath, isMain) {
  const rc = stat(requestPath);
  if (preserveSymlinks && !isMain) {
    return rc === 0 && path.resolve(requestPath);
  }
  return rc === 0 && toRealPath(requestPath);
}

function toRealPath(requestPath) {
  return fs.realpathSync(requestPath, {
    [internalFS.realpathCacheKey]: realpathCache
  });
}


/**
 * Given a path, check if the file exists with any of the set extensions
 * @param {*} p  文件绝对路径
 * @param {*} exts  允许的文件后缀名集合(一个数组)
 * @param {*} isMain  主程序入口
 */
function tryExtensions(p, exts, isMain) {
  for (let i = 0; i < exts.length; i++) {
    const filename = tryFile(p + exts[i], isMain);

    if (filename) {
      return filename;
    }
  }
  return false;
}

// Find the longest (possibly multi-dot) extension registered in
// Module._extensions
/**
 * 找到最长的且在Module._extensions中注册的文件后缀名
 * @param {*} filename  文件路径加文件名加后缀名
 */
function findLongestRegisteredExtension(filename) {
  const name = path.basename(filename);
  let currentExtension;
  let index;
  let startIndex = 0;
  while ((index = name.indexOf('.', startIndex)) !== -1) {
    startIndex = index + 1;
    if (index === 0) continue; // Skip dotfiles like .gitignore
    currentExtension = name.slice(index);
    if (Module._extensions[currentExtension]) return currentExtension;
  }
  return '.js';
}

// This only applies to requests of a specific form:
// 1. name/.*
// 2. @scope/name/.*
const EXPORTS_PATTERN = /^((?:@[^/\\%]+\/)?[^./\\%][^/\\%]*)(\/.*)?$/;

/**
 * 应用与特定格式的请求
 * @param {*} nmPath  当前处理的路径
 * @param {*} request  require参数
 * @param {*} absoluteRequest  request是否为绝对路径
 */
function resolveExports(nmPath, request, absoluteRequest) {
  // The implementation's behavior is meant to mirror resolution in ESM.
  if (experimentalExports && !absoluteRequest) {
    const [, name, expansion = ''] =
      StringPrototype.match(request, EXPORTS_PATTERN) || [];
    if (!name) {
      return path.resolve(nmPath, request);
    }

    const basePath = path.resolve(nmPath, name);
    const pkgExports = readPackageExports(basePath);
    const mappingKey = `.${expansion}`;

    if (typeof pkgExports === 'object' && pkgExports !== null) {
      if (ObjectPrototype.hasOwnProperty(pkgExports, mappingKey)) {
        const mapping = pkgExports[mappingKey];
        return resolveExportsTarget(pathToFileURL(basePath + '/'), mapping, '',
                                    basePath, mappingKey);
      }

      let dirMatch = '';
      for (const candidateKey of Object.keys(pkgExports)) {
        if (candidateKey[candidateKey.length - 1] !== '/') continue;
        if (candidateKey.length > dirMatch.length &&
            StringPrototype.startsWith(mappingKey, candidateKey)) {
          dirMatch = candidateKey;
        }
      }

      if (dirMatch !== '') {
        const mapping = pkgExports[dirMatch];
        const subpath = StringPrototype.slice(mappingKey, dirMatch.length);
        return resolveExportsTarget(pathToFileURL(basePath + '/'), mapping,
                                    subpath, basePath, mappingKey);
      }
    }
    if (mappingKey === '.' && typeof pkgExports === 'string') {
      return resolveExportsTarget(pathToFileURL(basePath + '/'), pkgExports,
                                  '', basePath, mappingKey);
    }
    if (pkgExports != null) {
      // eslint-disable-next-line no-restricted-syntax
      const e = new Error(`Package exports for '${basePath}' do not define ` +
          `a '${mappingKey}' subpath`);
      e.code = 'MODULE_NOT_FOUND';
      throw e;
    }
  }

  return path.resolve(nmPath, request);
}

function resolveExportsTarget(pkgPath, target, subpath, basePath, mappingKey) {
  if (typeof target === 'string') {
    if (target.startsWith('./') &&
        (subpath.length === 0 || target.endsWith('/'))) {
      const resolvedTarget = new URL(target, pkgPath);
      const pkgPathPath = pkgPath.pathname;
      const resolvedTargetPath = resolvedTarget.pathname;
      if (StringPrototype.startsWith(resolvedTargetPath, pkgPathPath) &&
          StringPrototype.indexOf(resolvedTargetPath, '/node_modules/',
                                  pkgPathPath.length - 1) === -1) {
        const resolved = new URL(subpath, resolvedTarget);
        const resolvedPath = resolved.pathname;
        if (StringPrototype.startsWith(resolvedPath, resolvedTargetPath) &&
            StringPrototype.indexOf(resolvedPath, '/node_modules/',
                                    pkgPathPath.length - 1) === -1) {
          return fileURLToPath(resolved);
        }
      }
    }
  } else if (Array.isArray(target)) {
    for (const targetValue of target) {
      if (typeof targetValue !== 'string') continue;
      try {
        return resolveExportsTarget(pkgPath, targetValue, subpath, basePath,
                                    mappingKey);
      } catch (e) {
        if (e.code !== 'MODULE_NOT_FOUND') throw e;
      }
    }
  }
  // eslint-disable-next-line no-restricted-syntax
  const e = new Error(`Package exports for '${basePath}' do not define a ` +
      `valid '${mappingKey}' target${subpath ? 'for ' + subpath : ''}`);
  e.code = 'MODULE_NOT_FOUND';
  throw e;
}

/**
 * @param request 模块id
 * @param paths  路径数组
 * @param isMain 主进程入口?
 */
Module._findPath = function(request, paths, isMain) {
  // path.isAbsolute() 方法检测 path 是否为绝对路径。
  const absoluteRequest = path.isAbsolute(request);
  if (absoluteRequest) {
    paths = [''];
  } else if (!paths || paths.length === 0) {
    return false;
  }

  //  构造缓存键
  const cacheKey = request + '\x00' +
                (paths.length === 1 ? paths[0] : paths.join('\x00'));
  // 从路径缓存中查找是否右缓存，有，则返回;无，进行下一步;
  const entry = Module._pathCache[cacheKey];
  if (entry)
    return entry;

  let exts;
  let trailingSlash = request.length > 0 &&
    request.charCodeAt(request.length - 1) === CHAR_FORWARD_SLASH;
  if (!trailingSlash) {
    trailingSlash = /(?:^|\/)\.?\.$/.test(request);
  }

  // For each path
  for (let i = 0; i < paths.length; i++) {
    // Don't search further if path doesn't exist
    const curPath = paths[i];
    // 调用internalModuleStat方法来判断文件或者文件夹是否存在，文件存在返回0，文件夹存在返回1，文件或文件夹不存在返回-2
    if (curPath && stat(curPath) < 1) continue;
    const basePath = resolveExports(curPath, request, absoluteRequest);
    let filename;

    const rc = stat(basePath);
    if (!trailingSlash) {
      if (rc === 0) {  // File. 若basePath是一个文件
        if (!isMain) {
          if (preserveSymlinks) { // 配置的参数值
              // 当解析和缓存模块时，命令模块加载器保持符号连接。
            filename = path.resolve(basePath);
          } else {
            // 不保持符号链接
            filename = toRealPath(basePath);
          }
        } else if (preserveSymlinksMain) {  // 参数值
          // For the main module, we use the preserveSymlinksMain flag instead
          // mainly for backward compatibility, as the preserveSymlinks flag
          // historically has not applied to the main module.  Most likely this
          // was intended to keep .bin/ binaries working, as following those
          // symlinks is usually required for the imports in the corresponding
          // files to resolve; that said, in some use cases following symlinks
          // causes bigger problems which is why the preserveSymlinksMain option
          // is needed.
          filename = path.resolve(basePath);
        } else {
          filename = toRealPath(basePath);
        }
      }

      if (!filename) {
        // Try it with each of the extensions
        if (exts === undefined)
        /**
         * Object.keys(obj) 将对象obj的属性构成数组
         * 
         * Module._extensions 允许加载的文件的后缀名数组
         */
          exts = Object.keys(Module._extensions);
          // 解析后缀名，返回文件url(添加上后缀名)
        filename = tryExtensions(basePath, exts, isMain);
      }
    }

    if (!filename && rc === 1) {  // Directory. 若basePath是一个目录
      // try it with each of the extensions at "index"
      if (exts === undefined)
        exts = Object.keys(Module._extensions);
        // 如果文件后缀不存在，则尝试加载该目录下的 package.json 中 main 入口指定的文件;如果不存在，然后尝试 index[.js, .node, .json] 文件
      filename = tryPackage(basePath, exts, isMain, request);
    }

    if (filename) {
      Module._pathCache[cacheKey] = filename;
      return filename;
    }
  }
  return false;
};

// 'node_modules' character codes reversed
const nmChars = [ 115, 101, 108, 117, 100, 111, 109, 95, 101, 100, 111, 110 ];
const nmLen = nmChars.length;
// 如果是windows平台
if (isWindows) {
  // 'from' is the __dirname of the module.
  /**
   * @param from  module的文件夹路径
   */
  Module._nodeModulePaths = function(from) {
    // 方法将路径或路径片段的序列解析为绝对路径
    // Guarantee(保证) that 'from' is absolute.
    from = path.resolve(from);

    // note: this approach（方法） *only* works when the path is guaranteed
    // to be absolute.  Doing a fully-edge-case-correct path.split
    // that works on both Windows and Posix is non-trivial.

    // return root node_modules when path is 'D:\\'.
    // path.resolve will make sure from.length >=3 in Windows.
    /**
     * CHAR_BACKWARD_SLASH: 字符 '\'
     * CHAR_COLON: 字符  ':'
     * 
     * 在windows D盘（不再任何子目录下）下执行path.resolve('.') 返回内容: D:\
     */
    if (from.charCodeAt(from.length - 1) === CHAR_BACKWARD_SLASH &&
        from.charCodeAt(from.length - 2) === CHAR_COLON)
        // 会返回 D:\\xxx\\xxx\\node_modules
      return [from + 'node_modules'];

    const paths = [];
    for (let i = from.length - 1, p = 0, last = from.length; i >= 0; --i) {
      const code = from.charCodeAt(i);
      // The path segment separator check ('\' and '/') was used to get
      // node_modules path for every path segment.
      // Use colon as an extra condition since we can get node_modules
      // path for drive root like 'C:\node_modules' and don't need to
      // parse drive name.
      if (code === CHAR_BACKWARD_SLASH ||
          code === CHAR_FORWARD_SLASH ||
          code === CHAR_COLON) {
        if (p !== nmLen)
          paths.push(from.slice(0, last) + '\\node_modules');
        last = i;
        p = 0;
      } else if (p !== -1) {
        if (nmChars[p] === code) {
          ++p;
        } else {
          p = -1;
        }
      }
    }

    /**
     * 输出内容:(在D盘的Share目录下执行)
     * D:\Share\node_modules
       D:\node_modules
     */
    return paths;
  };
} else { // posix
  // 'from' is the __dirname of the module.
  Module._nodeModulePaths = function(from) {
    // Guarantee that 'from' is absolute.
    from = path.resolve(from);
    // Return early not only to avoid unnecessary work, but to *avoid* returning
    // an array of two items for a root: [ '//node_modules', '/node_modules' ]
    if (from === '/')
      return ['/node_modules'];

    // note: this approach *only* works when the path is guaranteed
    // to be absolute.  Doing a fully-edge-case-correct path.split
    // that works on both Windows and Posix is non-trivial.
    const paths = [];
    for (let i = from.length - 1, p = 0, last = from.length; i >= 0; --i) {
      const code = from.charCodeAt(i);
      if (code === CHAR_FORWARD_SLASH) {
        if (p !== nmLen)
          paths.push(from.slice(0, last) + '/node_modules');
        last = i;
        p = 0;
      } else if (p !== -1) {
        if (nmChars[p] === code) {
          ++p;
        } else {
          p = -1;
        }
      }
    }

    // Append /node_modules to handle root paths.
    paths.push('/node_modules');

    /**
     * 在目录：/home/wei/WorkSpace/study/vue/vue-study/temp下执行代码
     * 输出内容:
     *        /home/wei/WorkSpace/study/vue/vue-study/temp/node_modules
              /home/wei/WorkSpace/study/vue/vue-study/node_modules
              /home/wei/WorkSpace/study/vue/node_modules
              /home/wei/WorkSpace/study/node_modules
              /home/wei/WorkSpace/node_modules
              /home/wei/node_modules
              /home/node_modules
              /node_modules
     */
    return paths;
  };
}

Module._resolveLookupPaths = function(request, parent) {
  // 判断该模块是否可以被用户加载
  if (NativeModule.canBeRequiredByUsers(request)) {
    debug('looking for %j in []', request);
    return null;
  }

  // 判断路径开头 不是相对路径 补充可能的路径（依赖包里的路径）
  // Check for node modules paths.
  if (request.charAt(0) !== '.' ||
      (request.length > 1 &&
      request.charAt(1) !== '.' &&
      request.charAt(1) !== '/' &&
      (!isWindows || request.charAt(1) !== '\\'))) {
    // modulePaths 是一个数组，目前还没有值，在哪里设置的值呢？
    let paths = modulePaths;
    if (parent != null && parent.paths && parent.paths.length) {
      paths = parent.paths.concat(paths);
    }

    debug('looking for %j in %j', request, paths);
    return paths.length > 0 ? paths : null;
  }

  /**
   * 调用者不存在，即核心模块加载
   */
  // With --eval, parent.id is not set and parent.filename is null.
  if (!parent || !parent.id || !parent.filename) {
    // Make require('./path/to/foo') work - normally the path is taken
    // from realpath(__filename) but with eval there is no filename
    const mainPaths = ['.'].concat(Module._nodeModulePaths('.'), modulePaths);

    debug('looking for %j in %j', request, mainPaths);
    return mainPaths;
  }

  debug('RELATIVE: requested: %s from parent.id %s', request, parent.id);

  /**
   * ath.dirname() 方法返回 path 的目录名
   * 
   * path.dirname('/foo/bar/baz/asdf/quux');
     // 返回: '/foo/bar/baz/asdf'
   */
  const parentDir = [path.dirname(parent.filename)];
  debug('looking for %j', parentDir);
  return parentDir;
};

// Check the cache for the requested file.
// 1. If a module already exists in the cache: return its exports object.
// 2. If the module is native: call
//    `NativeModule.prototype.compileForPublicLoader()` and return the exports.
// 3. Otherwise, create a new module for the file and save it to the cache.
//    Then have it load  the file contents before returning its exports
//    object.
/**
 * @param request id(即： 调用require方法传入的参数)
 * @param parent  调用require方法的Module
 * @param isMain  是否为主程序入口
 */
Module._load = function(request, parent, isMain) {
  let relResolveCacheIdentifier;
  // 为什么要判断parent是否存在
  if (parent) {
    debug('Module._load REQUEST %s parent: %s', request, parent.id);
    // Fast path for (lazy loaded) modules in the same directory. The indirect
    // caching is required to allow cache invalidation without changing the old
    // cache key names.
    // 同一目录下的快速访问。允许间接缓存失效而不改变就的缓存键的名称
    relResolveCacheIdentifier = `${parent.path}\x00${request}`;
    // 从自身(调用require方法的Module)的缓存中查找
    const filename = relativeResolveCache[relResolveCacheIdentifier];
    // 若自身(调用require方法的Module)缓存找不到，则去Module缓存中查找
    if (filename !== undefined) {
      // 使用js的以字符串访问对象的属性的方式去判断缓存中是否存在
      const cachedModule = Module._cache[filename];
      if (cachedModule !== undefined) {
        // 将加载的module添加到parent的children属性中去
        updateChildren(parent, cachedModule, true);
        return cachedModule.exports;
      }
      // 缓存失效，则从本地缓存中清除
      delete relativeResolveCache[relResolveCacheIdentifier];
    }
  }

  // 计算文件的绝对路径
  const filename = Module._resolveFilename(request, parent, isMain);

  // 以解析出来的绝对路径去全局缓存中查找，判断Module是否已经加载
  const cachedModule = Module._cache[filename];
  
  if (cachedModule !== undefined) {
    // 将加载的module添加到parent的children属性中去
    updateChildren(parent, cachedModule, true);
    return cachedModule.exports;
  }

  // 将filename当作内置模块来加载
  const mod = loadNativeModule(filename, request, experimentalModules);
  /**
   *  Set up NativeModule.
      function NativeModule(id) {
        this.filename = `${id}.js`;
        this.id = id;
        this.exports = {};
        this.module = undefined;
        this.exportKeys = undefined;
        this.loaded = false;
        this.loading = false;
        // 是否可以被用户加载
        this.canBeRequiredByUsers = !id.startsWith('internal/');
      }
   */
  if (mod && mod.canBeRequiredByUsers) return mod.exports;

  // 非内置模块，也没有被加载过，生成Module实例
  // Don't call updateChildren(), Module constructor already does.
  const module = new Module(filename, parent);

  // 是否为主进程
  if (isMain) {
    process.mainModule = module;
    module.id = '.';
  }
  // 将模块存入缓存(全局)
  Module._cache[filename] = module;
  if (parent !== undefined) {
    // 将模块存入缓存(自身，即调用require方法的module)
    relativeResolveCache[relResolveCacheIdentifier] = filename;
  }

  let threw = true;
  try {
    // Intercept(拦截) exceptions that occur during the first tick and rekey them
    // on error instance rather than module instance (which will immediately(立即) be
    // garbage collected(garbage collected:垃圾收集)).
    if (enableSourceMaps) {
      try {
        // 进行模块加载
        module.load(filename);
      } catch (err) {
        // Move source map from garbage collected module to alternate key.
        rekeySourceMap(Module._cache[filename], err);
        throw err; /* node-do-not-add-exception-line */
      }
    } else {
      module.load(filename);
    }
    threw = false;
  } finally {
    // 若加载的过程中出现异常，则需要清除之前创建的缓存
    if (threw) {
      delete Module._cache[filename];
      if (parent !== undefined) {
        delete relativeResolveCache[relResolveCacheIdentifier];
      }
    }
  }
  // 模块加载完毕，返回
  return module.exports;
};

Module._resolveFilename = function(request, parent, isMain, options) {
  // 判断模块是否可以被用户加载
  if (NativeModule.canBeRequiredByUsers(request)) {
    return request;
  }

  let paths;

  if (typeof options === 'object' && options !== null) {
    if (Array.isArray(options.paths)) {
      const isRelative = request.startsWith('./') ||
          request.startsWith('../') ||
          ((isWindows && request.startsWith('.\\')) ||
          request.startsWith('..\\'));

      if (isRelative) {
        paths = options.paths;
      } else {
        const fakeParent = new Module('', null);

        paths = [];

        for (let i = 0; i < options.paths.length; i++) {
          const path = options.paths[i];
          fakeParent.paths = Module._nodeModulePaths(path);
          const lookupPaths = Module._resolveLookupPaths(request, fakeParent);

          for (let j = 0; j < lookupPaths.length; j++) {
            if (!paths.includes(lookupPaths[j]))
              paths.push(lookupPaths[j]);
          }
        }
      }
    } else if (options.paths === undefined) {
      paths = Module._resolveLookupPaths(request, parent);
    } else {
      throw new ERR_INVALID_OPT_VALUE('options.paths', options.paths);
    }
  } else {
    paths = Module._resolveLookupPaths(request, parent);
  }

  // Look up the filename first, since that's the cache key. 取第一个文件路径作为缓存键
  const filename = Module._findPath(request, paths, isMain);
  if (!filename) {
    const requireStack = [];
    for (let cursor = parent;
      cursor;
      cursor = cursor.parent) {
      requireStack.push(cursor.filename || cursor.id);
    }
    let message = `Cannot find module '${request}'`;
    if (requireStack.length > 0) {
      message = message + '\nRequire stack:\n- ' + requireStack.join('\n- ');
    }
    // eslint-disable-next-line no-restricted-syntax
    const err = new Error(message);
    err.code = 'MODULE_NOT_FOUND';
    err.requireStack = requireStack;
    throw err;
  }
  return filename;
};


// Given a file name, pass it to the proper extension handler.
/**
 * 将他交给对应的处理程序去处理
 */
Module.prototype.load = function(filename) {
  debug('load %j for module %j', filename, this.id);

  assert(!this.loaded);
  this.filename = filename;
  // 找到当前文件夹的 node_modules
  this.paths = Module._nodeModulePaths(path.dirname(filename));

  // 找到该文件的后缀名
  const extension = findLongestRegisteredExtension(filename);
  /**
   * 执行特定的文件解析函数
   * 见如下的 
   * 1. Module._extensions['.js'] ，里面存在编译行为
   * 2. 。。。。。。
   */
  Module._extensions[extension](this, filename);
  this.loaded = true;

  if (experimentalModules) {
    const ESMLoader = asyncESM.ESMLoader;
    const url = `${pathToFileURL(filename)}`;
    const module = ESMLoader.moduleMap.get(url);
    // Create module entry at load time to snapshot exports correctly
    const exports = this.exports;
    // Called from cjs translator
    if (module !== undefined && module.module !== undefined) {
      if (module.module.getStatus() >= kInstantiated)
        module.module.setExport('default', exports);
    } else { // preemptively cache
      ESMLoader.moduleMap.set(
        url,
        new ModuleJob(ESMLoader, url, () =>
          new ModuleWrap(function() {
            this.setExport('default', exports);
          }, ['default'], url)
        )
      );
    }
  }
};


// Loads a module at the given file path. Returns that module's
// `exports` property.
Module.prototype.require = function(id) {
  validateString(id, 'id');
  if (id === '') {
    throw new ERR_INVALID_ARG_VALUE('id', id,
                                    'must be a non-empty string');
  }
  requireDepth++;
  try {
    return Module._load(id, this, /* isMain */ false);
  } finally {
    requireDepth--;
  }
};


// Resolved path to process.argv[1] will be lazily placed here
// (needed for setting breakpoint when called with --inspect-brk)
let resolvedArgv;
let hasPausedEntry = false;

// Run the file contents in the correct scope or sandbox. Expose
// the correct helper variables (require, module, exports) to
// the file.
// Returns exception, if any.
/**
 * 模块加载完成后，Node 使用 V8 引擎提供的方法构建运行沙箱，并执行函数代码
 */
Module.prototype._compile = function(content, filename) {
  let moduleURL;
  let redirects;
  if (manifest) {
    moduleURL = pathToFileURL(filename);
    redirects = manifest.getRedirector(moduleURL);
    manifest.assertIntegrity(moduleURL, content);
  }

  content = stripShebang(content);
  maybeCacheSourceMap(filename, content, this);

  let compiledWrapper;
  if (patched) {
    const wrapper = Module.wrap(content);
    compiledWrapper = vm.runInThisContext(wrapper, {
      filename,
      lineOffset: 0,
      displayErrors: true,
      importModuleDynamically: experimentalModules ? async (specifier) => {
        const loader = await asyncESM.loaderPromise;
        return loader.import(specifier, normalizeReferrerURL(filename));
      } : undefined,
    });
  } else {
    let compiled;
    try {
      compiled = compileFunction(
        content,
        filename,
        0,
        0,
        undefined,
        false,
        undefined,
        [],
        [
          'exports',
          'require',
          'module',
          '__filename',
          '__dirname',
        ]
      );
    } catch (err) {
      if (experimentalModules) {
        enrichCJSError(err);
      }
      throw err;
    }

    if (experimentalModules) {
      const { callbackMap } = internalBinding('module_wrap');
      callbackMap.set(compiled.cacheKey, {
        importModuleDynamically: async (specifier) => {
          const loader = await asyncESM.loaderPromise;
          return loader.import(specifier, normalizeReferrerURL(filename));
        }
      });
    }
    compiledWrapper = compiled.function;
  }

  let inspectorWrapper = null;
  if (getOptionValue('--inspect-brk') && process._eval == null) {
    if (!resolvedArgv) {
      // We enter the repl if we're not given a filename argument.
      if (process.argv[1]) {
        resolvedArgv = Module._resolveFilename(process.argv[1], null, false);
      } else {
        resolvedArgv = 'repl';
      }
    }

    // Set breakpoint on module start
    if (!hasPausedEntry && filename === resolvedArgv) {
      hasPausedEntry = true;
      inspectorWrapper = internalBinding('inspector').callAndPauseOnStart;
    }
  }
  const dirname = path.dirname(filename);
  /**
   * 使得Module this中可以使用require函数
   */
  const require = makeRequireFunction(this, redirects);
  let result;
  // 从这行代码可以看到，导出变量：module.export = xxx
  const exports = this.exports;
  const thisValue = exports;
  // 这就是js为什么可以使用module了 ， 导出变量：module.export = xxx
  const module = this;
  if (requireDepth === 0) statCache = new Map();
  if (inspectorWrapper) {
    result = inspectorWrapper(compiledWrapper, thisValue, exports,
                              require, module, filename, dirname);
  } else {
    // 执行模块中的函数
    result = compiledWrapper.call(thisValue, exports, require, module,
                                  filename, dirname);
  }
  if (requireDepth === 0) statCache = null;
  return result;
};

// Native extension for .js
let warnRequireESM = true;
Module._extensions['.js'] = function(module, filename) {
  if (filename.endsWith('.js')) {
    const pkg = readPackageScope(filename);
    if (pkg && pkg.data && pkg.data.type === 'module') {
      if (warnRequireESM) {
        const parentPath = module.parent && module.parent.filename;
        const basename = parentPath &&
            path.basename(filename) === path.basename(parentPath) ?
          filename : path.basename(filename);
        process.emitWarning(
          'require() of ES modules is not supported.\nrequire() of ' +
          `${filename} ${parentPath ? `from ${module.parent.filename} ` : ''}` +
          'is an ES module file as it is a .js file whose nearest parent ' +
          'package.json contains "type": "module" which defines all .js ' +
          'files in that package scope as ES modules.\nInstead rename ' +
          `${basename} to end in .cjs, change the requiring code to use ` +
          'import(), or remove "type": "module" from ' +
          `${path.resolve(pkg.path, 'package.json')}.`
        );
        warnRequireESM = false;
      }
      if (experimentalModules) {
        throw new ERR_REQUIRE_ESM(filename);
      }
    }
  }
  const content = fs.readFileSync(filename, 'utf8');
  module._compile(stripBOM(content), filename);
};


// Native extension for .json
Module._extensions['.json'] = function(module, filename) {
  const content = fs.readFileSync(filename, 'utf8');

  if (manifest) {
    const moduleURL = pathToFileURL(filename);
    manifest.assertIntegrity(moduleURL, content);
  }

  try {
    module.exports = JSON.parse(stripBOM(content));
  } catch (err) {
    err.message = filename + ': ' + err.message;
    throw err;
  }
};


// Native extension for .node
Module._extensions['.node'] = function(module, filename) {
  if (manifest) {
    const content = fs.readFileSync(filename);
    const moduleURL = pathToFileURL(filename);
    manifest.assertIntegrity(moduleURL, content);
  }
  // Be aware this doesn't use `content`
  return process.dlopen(module, path.toNamespacedPath(filename));
};

Module._extensions['.mjs'] = function(module, filename) {
  throw new ERR_REQUIRE_ESM(filename);
};

// Bootstrap main module.
Module.runMain = function() {
  // Load the main module--the command line argument.
  if (experimentalModules) {
    asyncESM.loaderPromise.then((loader) => {
      return loader.import(pathToFileURL(process.argv[1]).href);
    })
    .catch((e) => {
      internalBinding('errors').triggerUncaughtException(
        e,
        true /* fromPromise */
      );
    });
    return;
  }
  Module._load(process.argv[1], null, true);
};

function createRequireFromPath(filename) {
  // Allow a directory to be passed as the filename
  const trailingSlash =
    filename.endsWith('/') || (isWindows && filename.endsWith('\\'));

  const proxyPath = trailingSlash ?
    path.join(filename, 'noop.js') :
    filename;

  const m = new Module(proxyPath);
  m.filename = proxyPath;

  m.paths = Module._nodeModulePaths(m.path);
  return makeRequireFunction(m, null);
}

Module.createRequireFromPath = createRequireFromPath;

const createRequireError = 'must be a file URL object, file URL string, or ' +
  'absolute path string';

function createRequire(filename) {
  let filepath;

  if (filename instanceof URL ||
      (typeof filename === 'string' && !path.isAbsolute(filename))) {
    try {
      filepath = fileURLToPath(filename);
    } catch {
      throw new ERR_INVALID_ARG_VALUE('filename', filename,
                                      createRequireError);
    }
  } else if (typeof filename !== 'string') {
    throw new ERR_INVALID_ARG_VALUE('filename', filename, createRequireError);
  } else {
    filepath = filename;
  }
  return createRequireFromPath(filepath);
}

Module.createRequire = createRequire;

Module._initPaths = function() {
  const homeDir = isWindows ? process.env.USERPROFILE : safeGetenv('HOME');
  const nodePath = isWindows ? process.env.NODE_PATH : safeGetenv('NODE_PATH');

  // process.execPath is $PREFIX/bin/node except on Windows where it is
  // $PREFIX\node.exe where $PREFIX is the root of the Node.js installation.
  const prefixDir = isWindows ?
    path.resolve(process.execPath, '..') :
    path.resolve(process.execPath, '..', '..');

  let paths = [path.resolve(prefixDir, 'lib', 'node')];

  if (homeDir) {
    paths.unshift(path.resolve(homeDir, '.node_libraries'));
    paths.unshift(path.resolve(homeDir, '.node_modules'));
  }

  if (nodePath) {
    paths = nodePath.split(path.delimiter).filter(function pathsFilterCB(path) {
      return !!path;
    }).concat(paths);
  }

  modulePaths = paths;

  // Clone as a shallow copy, for introspection.
  Module.globalPaths = modulePaths.slice(0);
};

Module._preloadModules = function(requests) {
  if (!Array.isArray(requests))
    return;

  // Preloaded modules have a dummy parent module which is deemed to exist
  // in the current working directory. This seeds the search path for
  // preloaded modules.
  const parent = new Module('internal/preload', null);
  try {
    parent.paths = Module._nodeModulePaths(process.cwd());
  } catch (e) {
    if (e.code !== 'ENOENT') {
      throw e;
    }
  }
  for (let n = 0; n < requests.length; n++)
    parent.require(requests[n]);
};

Module.syncBuiltinESMExports = function syncBuiltinESMExports() {
  for (const mod of NativeModule.map.values()) {
    if (mod.canBeRequiredByUsers) {
      mod.syncExports();
    }
  }
};

// Backwards compatibility
Module.Module = Module;

// We have to load the esm things after module.exports!
if (experimentalModules) {
  asyncESM = require('internal/process/esm_loader');
  ModuleJob = require('internal/modules/esm/module_job');
  ({ ModuleWrap, kInstantiated } = internalBinding('module_wrap'));
}
