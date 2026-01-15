"use client";

interface CodeEditorProps {
    value: string;
    onChange?: (value: string) => void;
    readOnly?: boolean;
    label: string;
}

export default function CodeEditor({ value, onChange, readOnly = false, label }: CodeEditorProps) {
    return (
        <div className="flex flex-col h-full">
            <label className="text-gray-400 text-sm font-semibold mb-2 uppercase tracking-wide">{label}</label>
            <textarea
                className={`flex-1 w-full bg-gray-900 text-gray-100 font-mono p-4 rounded-lg border border-gray-700 focus:outline-none focus:ring-2 focus:ring-blue-500 resize-none ${readOnly ? "opacity-90 cursor-not-allowed" : ""
                    }`}
                value={value}
                onChange={(e) => onChange?.(e.target.value)}
                readOnly={readOnly}
                spellCheck={false}
            />
        </div>
    );
}
