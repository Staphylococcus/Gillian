/*! Derived from JSON3 v3.2.6, Copyright 2012-2013 Kit Cambridge, MIT. See README.md and LICENSE. */
(function (JSON3) {
  "use strict";

  var getClass = Object.prototype.toString,
    undef;
  var functionClass = "[object Function]",
    numberClass = "[object Number]";
  var stringClass = "[object String]",
    arrayClass = "[object Array]",
    booleanClass = "[object Boolean]";
  function define(object, key, value) {
    Object.defineProperty(object, key, {
      value: value,
      writable: true,
      enumerable: true,
      configurable: true
    });
  }
  function forEachKey(keys, callback) {
    for (var i = 0; i < keys.length; i++) callback(keys[i]);
  }
  function forEach(object, callback) {
    forEachKey(Object.keys(object), callback);
  }
  function hex(unit) {
    var digits = "0123456789abcdef";
    return digits[unit >>> 12 & 15] + digits[unit >>> 8 & 15] + digits[unit >>> 4 & 15] + digits[unit & 15];
  }
  var Escapes = {
    92: "\\\\",
    34: "\\\"",
    8: "\\b",
    12: "\\f",
    10: "\\n",
    13: "\\r",
    9: "\\t"
  };
  var quote = function (value) {
    var result = "\"",
      index = 0,
      length = value.length;
    for (; index < length; index++) {
      var charCode = value.charCodeAt(index);
      switch (charCode) {
        case 8:
        case 9:
        case 10:
        case 12:
        case 13:
        case 34:
        case 92:
          result += Escapes[charCode];
          break;
        default:
          if (charCode < 32) {
            result += "\\u" + hex(charCode);
            break;
          }
          if (charCode >= 0xd800 && charCode <= 0xdbff && !(value.charCodeAt(index + 1) >= 0xdc00 && value.charCodeAt(index + 1) <= 0xdfff) || charCode >= 0xdc00 && charCode <= 0xdfff && !(value.charCodeAt(index - 1) >= 0xd800 && value.charCodeAt(index - 1) <= 0xdbff)) {
            result += "\\u" + hex(charCode);
            break;
          }
          result += value[index];
      }
    }
    return result + "\"";
  };
  var serialize = function (property, object, callback, properties, whitespace, indentation, stack) {
    var value, className, results, element, index, length, prefix, result;
    value = object[property];
    if (value !== null && (typeof value == "object" || typeof value == "function")) {
      var toJSON = value.toJSON;
      if (typeof toJSON == "function") value = toJSON.call(value, "" + property);
    }
    if (callback) {
      value = callback.call(object, "" + property, value);
    }
    if (value === null) {
      return "null";
    }
    className = getClass.call(value);
    if (className == booleanClass) {
      return Boolean.prototype.valueOf.call(value) ? "true" : "false";
    } else if (className == numberClass) {
      value = Number(value);
      return value > -1 / 0 && value < 1 / 0 ? "" + value : "null";
    } else if (className == stringClass) {
      return quote(String(value));
    }
    if (typeof value == "object") {
      for (length = stack.length; length--;) {
        if (stack[length] === value) {
          throw TypeError();
        }
      }
      stack.push(value);
      results = [];
      prefix = indentation;
      indentation += whitespace;
      if (className == arrayClass) {
        for (index = 0, length = value.length; index < length; index++) {
          element = serialize(index, value, callback, properties, whitespace, indentation, stack);
          results.push(element === undef ? "null" : element);
        }
        result = results.length ? whitespace ? "[\n" + indentation + results.join(",\n" + indentation) + "\n" + prefix + "]" : "[" + results.join(",") + "]" : "[]";
      } else {
        forEachKey(properties || Object.keys(value), function (property) {
          var element = serialize(property, value, callback, properties, whitespace, indentation, stack);
          if (element !== undef) {
            results.push(quote(property) + ":" + (whitespace ? " " : "") + element);
          }
        });
        result = results.length ? whitespace ? "{\n" + indentation + results.join(",\n" + indentation) + "\n" + prefix + "}" : "{" + results.join(",") + "}" : "{}";
      }
      stack.pop();
      return result;
    }
  };
  JSON3.stringify = function (source, filter, width) {
    var whitespace = "",
      callback,
      properties,
      className,
      value;
    if (typeof filter == "function" || typeof filter == "object" && filter) {
      if ((className = getClass.call(filter)) == functionClass) {
        callback = filter;
      } else if (className == arrayClass) {
        properties = [];
        for (var index = 0, length = filter.length, value; index < length; index++) {
          value = filter[index];
          className = getClass.call(value);
          if (className == stringClass || className == numberClass) {
            value = String(value);
            if (properties.indexOf(value) < 0) properties.push(value);
          }
        }
      }
    }
    className = getClass.call(width);
    if (className == numberClass) {
      width = Math.min(10, Math.floor(Number(width)));
      for (whitespace = ""; whitespace.length < width; whitespace += " ");
    } else if (className == stringClass) {
      whitespace = String(width).slice(0, 10);
    }
    return serialize("", (value = {}, value[""] = source, value), callback, properties, whitespace, "", []);
  };
  var fromCharCode = String.fromCharCode;
  var Unescapes = {
    92: "\\",
    34: "\"",
    47: "/",
    98: "\b",
    116: "\t",
    110: "\n",
    102: "\f",
    114: "\r"
  };
  var Index, Source;
  var abort = function () {
    Index = Source = null;
    throw SyntaxError();
  };
  var lex = function () {
    var source = Source,
      length = source.length,
      value,
      begin,
      position,
      isSigned,
      charCode;
    while (Index < length) {
      charCode = source.charCodeAt(Index);
      switch (charCode) {
        case 9:
        case 10:
        case 13:
        case 32:
          Index++;
          break;
        case 123:
        case 125:
        case 91:
        case 93:
        case 58:
        case 44:
          value = source[Index];
          Index++;
          return value;
        case 34:
          for (value = "@", Index++; Index < length;) {
            charCode = source.charCodeAt(Index);
            if (charCode < 32) {
              abort();
            } else if (charCode == 92) {
              charCode = source.charCodeAt(++Index);
              switch (charCode) {
                case 92:
                case 34:
                case 47:
                case 98:
                case 116:
                case 110:
                case 102:
                case 114:
                  value += Unescapes[charCode];
                  Index++;
                  break;
                case 117:
                  begin = ++Index;
                  for (position = Index + 4; Index < position; Index++) {
                    charCode = source.charCodeAt(Index);
                    if (!(charCode >= 48 && charCode <= 57 || charCode >= 97 && charCode <= 102 || charCode >= 65 && charCode <= 70)) {
                      abort();
                    }
                  }
                  value += fromCharCode("0x" + source.slice(begin, Index));
                  break;
                default:
                  abort();
              }
            } else {
              if (charCode == 34) {
                break;
              }
              charCode = source.charCodeAt(Index);
              begin = Index;
              while (charCode >= 32 && charCode != 92 && charCode != 34) {
                charCode = source.charCodeAt(++Index);
              }
              value += source.slice(begin, Index);
            }
          }
          if (source.charCodeAt(Index) == 34) {
            Index++;
            return value;
          }
          abort();
        default:
          begin = Index;
          if (charCode == 45) {
            isSigned = true;
            charCode = source.charCodeAt(++Index);
          }
          if (charCode >= 48 && charCode <= 57) {
            if (charCode == 48 && (charCode = source.charCodeAt(Index + 1), charCode >= 48 && charCode <= 57)) {
              abort();
            }
            isSigned = false;
            for (; Index < length && (charCode = source.charCodeAt(Index), charCode >= 48 && charCode <= 57); Index++);
            if (source.charCodeAt(Index) == 46) {
              position = ++Index;
              for (; position < length && (charCode = source.charCodeAt(position), charCode >= 48 && charCode <= 57); position++);
              if (position == Index) {
                abort();
              }
              Index = position;
            }
            charCode = source.charCodeAt(Index);
            if (charCode == 101 || charCode == 69) {
              charCode = source.charCodeAt(++Index);
              if (charCode == 43 || charCode == 45) {
                Index++;
              }
              for (position = Index; position < length && (charCode = source.charCodeAt(position), charCode >= 48 && charCode <= 57); position++);
              if (position == Index) {
                abort();
              }
              Index = position;
            }
            return +source.slice(begin, Index);
          }
          if (isSigned) {
            abort();
          }
          if (source.slice(Index, Index + 4) == "true") {
            Index += 4;
            return true;
          } else if (source.slice(Index, Index + 5) == "false") {
            Index += 5;
            return false;
          } else if (source.slice(Index, Index + 4) == "null") {
            Index += 4;
            return null;
          }
          abort();
      }
    }
    return "$";
  };
  var get = function (value) {
    var results, hasMembers;
    if (value == "$") {
      abort();
    }
    if (typeof value == "string") {
      if (value[0] == "@") {
        return value.slice(1);
      }
      if (value == "[") {
        results = [];
        for (;; hasMembers || (hasMembers = true)) {
          value = lex();
          if (value == "]") {
            break;
          }
          if (hasMembers) {
            if (value == ",") {
              value = lex();
              if (value == "]") {
                abort();
              }
            } else {
              abort();
            }
          }
          if (value == ",") {
            abort();
          }
          results.push(get(value));
        }
        return results;
      } else if (value == "{") {
        results = {};
        for (;; hasMembers || (hasMembers = true)) {
          value = lex();
          if (value == "}") {
            break;
          }
          if (hasMembers) {
            if (value == ",") {
              value = lex();
              if (value == "}") {
                abort();
              }
            } else {
              abort();
            }
          }
          if (value == "," || typeof value != "string" || value[0] != "@" || lex() != ":") {
            abort();
          }
          define(results, value.slice(1), get(lex()));
        }
        return results;
      }
      abort();
    }
    return value;
  };
  var update = function (source, property, callback) {
    var element = walk(source, property, callback);
    if (element === undef) {
      delete source[property];
    } else {
      define(source, property, element);
    }
  };
  var walk = function (source, property, callback) {
    var value = source[property],
      length;
    if (typeof value == "object" && value) {
      if (getClass.call(value) == arrayClass) {
        for (var index = 0, length = value.length; index < length; index++) {
          update(value, "" + index, callback);
        }
      } else {
        forEach(value, function (property) {
          update(value, property, callback);
        });
      }
    }
    return callback.call(source, property, value);
  };
  JSON3.parse = function (source, callback) {
    var result, value;
    Index = 0;
    Source = String(source);
    result = get(lex());
    if (lex() != "$") {
      abort();
    }
    Index = Source = null;
    return callback && getClass.call(callback) == functionClass ? walk((value = {}, value[""] = result, value), "", callback) : result;
  };
})(JSON);

"use strict";
/* P09 serializer: number text + negative-zero + extreme finite + non-finite.
   Node oracle:
     JSON.stringify(-0) === "0"
     JSON.stringify(5e-324) === "5e-324"
     JSON.stringify(9007199254740992) === "9007199254740992"
     JSON.stringify(NaN) === "null"
     JSON.stringify(Infinity) === "null"
     JSON.stringify(-Infinity) === "null" */
var okZero = JSON.stringify(-0) === "0";
var okSub = JSON.stringify(5e-324) === "5e-324";
var okBig = JSON.stringify(9007199254740992) === "9007199254740992";
var okNaN = JSON.stringify(NaN) === "null";
var okInf = JSON.stringify(Infinity) === "null";
var okNInf = JSON.stringify(-Infinity) === "null";
Assert(okZero);
Assert(okSub);
Assert(okBig);
Assert(okNaN);
Assert(okInf);
Assert(okNInf);
