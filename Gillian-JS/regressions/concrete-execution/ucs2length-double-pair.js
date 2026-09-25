"use strict";
function ucs2length(str) {
        var len = str.length;
        var length = 0;
        var pos = 0;
        var value;
        while (pos < len) {
          length++;
          value = str.charCodeAt(pos++);
          if (value >= 55296 && value <= 56319 && pos < len) {
            value = str.charCodeAt(pos);
            if ((value & 64512) === 56320) { pos++; length++; }
          }
        }
        return length;
      }
var result = ucs2length("𝠊");
if (result !== 1) throw "wrong exact Unicode count: " + result;
"unreachable";
