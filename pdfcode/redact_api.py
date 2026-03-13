from flask import Flask, request, send_file, Response
import requests
import fitz  # PyMuPDF
import io
from urllib.parse import parse_qs
from uuid import uuid4

app = Flask(__name__)

def split_url(url):
    pdf_index = url.lower().find('.pdf')
    if pdf_index == -1:
        return url, ''
    part1 = url[:pdf_index + 4]  # Include ".pdf"
    part2 = url[pdf_index + 4:]  # Everything after ".pdf"
    return part1.strip(), part2.strip()

def extract_temp_id(query_string):
    params = parse_qs(query_string)
    return params.get("temp_id", [""])[0]

@app.route('/redact-pdf', methods=['GET'])
def redact_pdf():
    try:
        pdf_url = request.args.get('pdf_url')
        if not pdf_url:
            return Response("Missing pdf_url parameter", status=400)

        pdf_base_url, query_string = split_url(pdf_url)
        temp_id = request.args.get('temp_id') or extract_temp_id(query_string)
        if not temp_id:
            return Response("Missing temp_id parameter", status=400)

        response = requests.get(pdf_base_url, timeout=10)
        if response.status_code != 200:
            return Response(f"Failed to download PDF: {response.text}", status=response.status_code)

        pdf_data = io.BytesIO(response.content)
        doc = fitz.open(stream=pdf_data, filetype="pdf")

        api_url = f"https://idms-dev.blockchaincloudapps.com/api/v1/get-pdf-viewer-redact-info?temp_id={temp_id}"
        headers = {'Content-Type': 'application/json'}
        redact_response = requests.get(api_url, headers=headers, timeout=10)

        if redact_response.status_code != 200:
            return Response(f"Failed to fetch redaction data: {redact_response.text}", status=redact_response.status_code)

        redact_data = redact_response.json()
        results = [(item["coordinate"], item["page_size"], item["zoom_size"]) for item in redact_data["data"]]

        for coord_str, saved_pagesize_str, _ in results:
            coord = eval(coord_str)
            saved_pagesize = eval(saved_pagesize_str)
            page_num = coord['page']

            page = doc.load_page(page_num)
            actual_width, actual_height = page.rect.width, page.rect.height

            scale_x = actual_width / saved_pagesize[0]
            scale_y = actual_height / saved_pagesize[1]

            x1 = coord['x1'] * scale_x
            y1 = coord['y1'] * scale_y
            x2 = coord['x2'] * scale_x
            y2 = coord['y2'] * scale_y

            rect = fitz.Rect(x1, y1, x2, y2)

            shape = page.new_shape()
            if coord.get('filled', True):
                shape.draw_rect(rect)
                shape.finish(fill=(0, 0, 0), color=None)
            else:
                shape.draw_rect(rect)
                shape.finish(color=(0, 0, 0), fill=None)

            shape.commit()

        redacted_pdf = io.BytesIO()
        doc.save(redacted_pdf)
        doc.close()
        redacted_pdf.seek(0)

        return send_file(
            redacted_pdf,
            mimetype='application/pdf',
            as_attachment=True,
            download_name=f'redacted_{uuid4()}.pdf'
        )

    except Exception as e:
        return Response(f"Error during redaction: {str(e)}", status=500)

if __name__ == '__main__':
    app.run(debug=True)